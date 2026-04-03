#lang racket/base
(require "match.rkt"
         "wrap.rkt"
         "known.rkt")

(provide apply-cse)



(define (common-scope lst1 lst2)
  (cond
    [(or (null? lst1) (null? lst2)) '()]
    [(equal? (car lst1) (car lst2))
     (cons (car lst1) (common-scope (cdr lst1) (cdr lst2)))]
    [(and (pair? (car lst1)) (eq? 'seq (car (car lst1)))
          (pair? (car lst2)) (eq? 'seq (car (car lst2))))
     (let ([n1 (cadr (car lst1))]
           [n2 (cadr (car lst2))])
       (list `(seq ,(min n1 n2))))]
    [else '()]))


(define (scp-ext scp idx)
  (append scp (list idx)))


(define (lst-last lst)
  (if (null? (cdr lst))
      (car lst)
      (lst-last (cdr lst))))


(define (seq-element? x)
  (match x
    [`(seq ,_) #t]
    [`,_ #f]))




;; ============================================================
;; Main entry point

(define (apply-cse body prim-knowns)
  (map (lambda (form) (cse-single form prim-knowns)) body))


(struct cse-defval (bindings inst) #:transparent)

(define (cse-single form prim-knowns)

  (define (pure-rator? rator)
    (let ([r (unwrap rator)])
      (and (symbol? r)
           (let ([v (hash-ref prim-knowns r #f)])
             (and v
                  (or (known-procedure/pure? v)
                      (known-procedure/allocates? v)
                      (known-procedure/folding? v)
                      (known-procedure/then-pure? v)))))))

  (define impure-ids (make-hash))
  (define expr2sym (make-hash))
  (define sym2expr (make-hash))
  (define sym-impure (make-hash))
  (define sym2scp (make-hash))
  (define sym-duplicate (make-hash))
  (define scp2dupsyms (make-hash))

  ;; --------------------------------------------------------
  ;; Generic traversal with result-handler callback
  ;;
  ;; `result-handler` is called as (result-handler new-expr purity scope)
  ;; and must return a list of forms (usually `(list expr)`, or
  ;; `(list def ... expr)` when splicing bindings at a seq position).

  (define (concat-insts subexprs)
    (match subexprs
      [`(,e . ,es) (if (cse-defval? e)
                       (list `(let-values ,(cse-defval-bindings e)
                                ,@(cons (cse-defval-inst e) (concat-insts es))))
                       (cons e (concat-insts es)))]
      [`() '()]))

  (define (primitive? v)
    (or (number? v) (boolean? v) (string? v) (char? v) (bytes? v)))

  (define (subexprs-purity subexprs)
    (for/and ([se (in-list subexprs)])
      (cond
        [(primitive? se) #t]
        [(symbol? se) (not (hash-ref sym-impure se #f))]
        [(hash-ref expr2sym se #f) => (lambda (sym) (not (hash-ref sym-impure sym #f)))]
        [else #f])))

  (define (traverse-expr! e scope result-handler)
    (define (traverse-subexpr sub idx)
      (traverse-expr! sub (scp-ext scope idx) result-handler))

    (define (traverse-subexprs subs idx-start seq?)
      (concat-insts (for/list ([sub (in-list subs)]
                               [i (in-naturals idx-start)])
                      (define new-scp (if seq? `(seq ,i) i))
                      (traverse-expr! sub (scp-ext scope new-scp) result-handler))))



    (cond
      [(and (symbol? e) (duplicate-and-pure? e))
       (result-handler e #t scope)]
      [(and (symbol? e) (hash-has-key? sym2expr e))
       (traverse-expr! (hash-ref sym2expr e) scope result-handler)]
      [else
       (match e
         [`(lambda ,formals ,body ...)
          (let* ([new-body (traverse-subexprs body 0 #t)]
                 [new-e `(lambda ,formals ,@new-body)]
                 [purity (subexprs-purity new-body)])
            (result-handler new-e purity scope))]
         [`(case-lambda [,formalss ,bodys ...] ...)
          (let* ([new-clauses
                  (for/list ([formals (in-list formalss)]
                             [body (in-list bodys)]
                             [i (in-naturals)])
                    (define clause-body
                      (concat-insts (for/list ([b (in-list body)]
                                               [j (in-naturals)])
                                      (traverse-expr! b (scp-ext (scp-ext scope i) `(seq ,j))
                                                      result-handler))))
                    `(,formals ,@clause-body))]
                 [new-e `(case-lambda ,@new-clauses)]
                 [purity (subexprs-purity (apply append (map cdr new-clauses)))])
            (result-handler new-e purity scope))]
         [`(define-values ,ids ,rhs)
          (let* ([new-rhs (traverse-subexpr rhs 0)]
                 [new-e `(define-values ,ids ,new-rhs)]
                 [purity #f])
            (result-handler new-e purity scope))]
         [`(quote ,_) e]
         [`(let-values ([,idss ,rhss] ...) ,bodys ...)
          (let* ([new-clauses
                  (for/list ([ids (in-list idss)]
                             [rhs (in-list rhss)]
                             [i (in-naturals)])
                    (list ids (traverse-subexpr rhs i)))]
                 [body-start (length new-clauses)]
                 [new-body (traverse-subexprs bodys body-start #t)]
                 [new-e `(let-values ,new-clauses ,@new-body)]
                 [purity (and (subexprs-purity (map cadr new-clauses))
                              (subexprs-purity new-body))])
            (result-handler new-e purity scope))]
         [`(letrec-values ([,idss ,rhss] ...) ,bodys ...)
          (let* ([new-clauses
                  (for/list ([ids (in-list idss)]
                             [rhs (in-list rhss)]
                             [i (in-naturals)])
                    (list ids (traverse-subexpr rhs i)))]
                 [body-start (length new-clauses)]
                 [new-body (traverse-subexprs bodys body-start #t)]
                 [new-e `(letrec-values ,new-clauses ,@new-body)]
                 [purity (and (subexprs-purity (map cadr new-clauses))
                              (subexprs-purity new-body))])
            (result-handler new-e purity scope))]
         [`(if ,tst ,thn ,els)
          (let* ([new-tst (traverse-subexpr tst 0)]
                 [new-thn (traverse-subexpr thn 1)]
                 [new-els (traverse-subexpr els 2)]
                 [new-e `(if ,new-tst ,new-thn ,new-els)]
                 [purity (subexprs-purity (list new-tst new-thn new-els))])
            (result-handler new-e purity scope))]
         [`(with-continuation-mark ,key ,val ,body)
          (let* ([new-key (traverse-subexpr key 0)]
                 [new-val (traverse-subexpr val 1)]
                 [new-body (traverse-subexpr body 2)]
                 [new-e `(with-continuation-mark ,new-key ,new-val ,new-body)]
                 [purity (subexprs-purity (list new-key new-val new-body))])
            (result-handler new-e purity scope))]
         [`(begin ,exps ...)
          (let* ([new-body (traverse-subexprs exps 0 #t)]
                 [new-e `(begin ,@new-body)]
                 [purity (subexprs-purity new-body)])
            (result-handler new-e purity scope))]
         [`(begin-unsafe ,exps ...)
          (let* ([new-body (traverse-subexprs exps 0 #t)]
                 [new-e `(begin-unsafe ,@new-body)]
                 [purity (subexprs-purity new-body)])
            (result-handler new-e purity scope))]
         [`(begin0 ,exps ...)
          (let* ([new-body (traverse-subexprs exps 0 #t)]
                 [new-e `(begin0 ,@new-body)]
                 [purity (subexprs-purity new-body)])
            (result-handler new-e purity scope))]
         [`(set! ,id ,rhs)
          (let* ([new-rhs (traverse-subexpr rhs 0)]
                 [new-e `(set! ,id ,new-rhs)]
                 [purity #f])
            (result-handler new-e purity scope))]
         [`(variable-reference-constant? ,_) e]
         [`(variable-reference-from-unsafe? ,_) e]
         [`(#%variable-reference . ,_) e]
         ;;;  [`(void ,_ ...) e]
         [`(,rator ,exps ...)
          (let* ([new-args (traverse-subexprs exps 0 #f)]
                 [new-e `(,rator ,@new-args)]
                 [purity (and (pure-rator? rator)
                              (subexprs-purity new-args))])
            (result-handler new-e purity scope))]
         [`,_ e])]))

  ;; --------------------------------------------------------
  ;; Pass 1 handler: collect set!-mutated identifiers

  (define (collect-impure! e . _)
    (match e
      [`(set! ,id ,_) (hash-set! impure-ids (unwrap id) #t)]
      [`,_ (void)])
    e)

  ;; --------------------------------------------------------
  ;; Pass 2 handler: record expression/scope mappings

  (define (record-expr! expr purity scp)
    (cond
      [(hash-has-key? expr2sym expr)
       (define sym (hash-ref expr2sym expr))
       (hash-set! sym-duplicate sym #t)
       (hash-set! sym2scp sym (common-scope (hash-ref sym2scp sym) scp))
       sym]
      [else
       (define sym (gensym 'cse))
       (hash-set! expr2sym expr sym)
       (hash-set! sym2expr sym expr)
       (hash-set! sym2scp sym scp)
       (hash-set! sym-impure sym (not purity))
       sym]))

  ;; --------------------------------------------------------
  ;; Build scp2dupsyms mapping

  (define (duplicate-and-pure? sym)
    (and (hash-has-key? sym-duplicate sym)
         (not (hash-ref sym-impure sym #f))))

  (define (init-scp2dupsyms!)
    (for ([sym (in-hash-keys sym2scp)])
      (define scp (hash-ref sym2scp sym))
      (when (duplicate-and-pure? sym)
        (hash-set! scp2dupsyms scp
                   (cons sym (hash-ref scp2dupsyms scp '()))))))

  ;; --------------------------------------------------------
  ;; Pass 3 handler: reconstruct, inserting bindings for duplicates

  ;; Expand CSE gensyms in an expression back to original sub-expressions,
  ;; so the let-values RHS doesn't contain unbound internal gensyms.
  (define (expand-cse-expr e)
    (cond
      [(and (symbol? e) (hash-has-key? sym2expr e))
       (expand-cse-expr (hash-ref sym2expr e))]
      [(pair? e) (cons (expand-cse-expr (car e)) (expand-cse-expr (cdr e)))]
      [else e]))

  (define (reconstruct expr purity scp)
    (define dupsyms (hash-ref scp2dupsyms scp #f))

    (if (not dupsyms)
        expr
        (cond
          [(and (pair? scp) (seq-element? (lst-last scp)))
           (cse-defval
             (for/list ([sym (in-list dupsyms)])
               `((,sym) ,(expand-cse-expr (hash-ref sym2expr sym))))
             expr)]
          [else
           `(let-values
              ,(for/list ([sym (in-list dupsyms)])
                 `((,sym) ,(expand-cse-expr (hash-ref sym2expr sym))))
              ,expr)])))

  ;; --------------------------------------------------------
  ;; Run passes



  (traverse-expr! form '() collect-impure!)
  (define pass2 (traverse-expr! form '() record-expr!))
  (init-scp2dupsyms!)
  (define res (traverse-expr! pass2 '() reconstruct))


  ;;; (match form
  ;;;   [`(call-with-values
  ;;;       (lambda ()
  ;;;         (let-values (((x_1) 1))
  ;;;           (+ (let-values (((y_2) 2))
  ;;;                (+ (+ (+ y_2 1) (+ y_2 1))
  ;;;                   (+ x_1 2)))
  ;;;              (let-values (((z_3) 3))
  ;;;                (+ z_3 (+ x_1 2))))))
  ;;;       print-values)


  (define (deep-unwrap v)
    (cond
      [(pair? v) (cons (deep-unwrap (car v)) (deep-unwrap (cdr v)))]
      [else (let ([u (unwrap v)]) (if (pair? u) (deep-unwrap u) u))]))

  (log-error (format "cse input: ~s" (deep-unwrap form)))

  (log-error (format "cse result: ~s" (deep-unwrap res)))

  ;;; (log-error (format "+ is pure?: ~a" (pure-rator? '+)))

  ;;; (log-error (format "prim-knowns:")
  ;;;            (for ([k (in-hash-keys prim-knowns)])
  ;;;              (log-error (format "  ~a -> ~a" k (hash-ref prim-knowns k)))))
  ;;;   ]
  ;;; [`,_ (void)])

  ;;; (displayln "impure ids:")
  ;;; (for ([id (in-hash-keys impure-ids)])
  ;;;   (displayln id))
  ;;; (displayln "")

  ;;; (displayln "expr2sym:")
  ;;; (for ([expr (in-hash-keys expr2sym)])
  ;;;   (displayln (format "~a -> ~a" expr (hash-ref expr2sym expr))))
  ;;; (displayln "")

  ;;; (displayln "sym2expr:")
  ;;; (for ([sym (in-hash-keys sym2expr)])
  ;;;   (displayln (format "~a -> ~a" sym (hash-ref sym2expr sym))))
  ;;; (displayln "")

  ;;; (displayln "sym-impure:")
  ;;; (for ([sym (in-hash-keys sym-impure)])
  ;;;   (displayln (format "~a -> ~a" sym (hash-ref sym-impure sym))))
  ;;; (displayln "")

  ;;; (displayln "sym2scp:")
  ;;; (for ([sym (in-hash-keys sym2scp)])
  ;;;   (displayln (format "~a -> ~a" sym (hash-ref sym2scp sym))))
  ;;; (displayln "")

  ;;; (displayln "sym-duplicate:")
  ;;; (for ([sym (in-hash-keys sym-duplicate)])
  ;;;   (displayln (format "~a -> ~a" sym (hash-ref sym-duplicate sym))))
  ;;; (displayln "")

  ;;; (displayln "scp2dupsyms:")
  ;;; (for ([scp (in-hash-keys scp2dupsyms)])
  ;;;   (displayln (format "~a -> ~a" scp (hash-ref scp2dupsyms scp))))
  ;;; (displayln "")

  ;;; (displayln "prim-knowns")
  ;;; (for ([k (in-hash-keys prim-knowns)])
  ;;;   (displayln (format "~a -> ~a" k (hash-ref prim-knowns k))))
  ;;; (displayln "")

  res

  )
