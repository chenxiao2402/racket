#lang racket/base
(require "match.rkt"
         "wrap.rkt")

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
       (cons `(seq ,(min n1 n2)) (common-scope (cdr lst1) (cdr lst2))))]
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

(define (apply-cse body)
  (map cse-single body))


(define (cse-single form)

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
  ;; `result-handler` is called as (result-handler new-expr impurity scope)
  ;; and must return a list of forms (usually `(list expr)`, or
  ;; `(list def ... expr)` when splicing bindings at a seq position).

  (define (concat-insts subexprs)
    (match subexprs
      [`(,e . ,es) (if (list? e)
                       (append e (concat-insts es))
                       (cons e (concat-insts es)))]
      [`() '()]))

  (define (subexprs-impurity subexprs)
    (for/or ([se (in-list subexprs)])
      (let ([sym (hash-ref expr2sym se #f)])
        (and sym (hash-ref sym-impure sym #f)))))

  (define (traverse-expr! e scope result-handler)
    (define (traverse-subexpr sub idx)
      (traverse-expr! sub (scp-ext scope idx) result-handler))

    (define (traverse-subexprs subs idx-start seq?)
      (concat-insts (for/list ([sub (in-list subs)]
                               [i (in-naturals idx-start)])
                      (define new-scp (if seq? `(seq ,i) i))
                      (traverse-expr! sub (scp-ext scope new-scp) result-handler))))

    (if (and (symbol? e) (hash-has-key? sym2expr e))
        (traverse-expr! (hash-ref sym2expr e) scope result-handler)
        (match e
          [`(lambda ,formals ,body ...)
           (let* ([new-body (traverse-subexprs body 0 #t)]
                  [new-e `(lambda ,formals ,@new-body)]
                  [impurity (subexprs-impurity new-body)])
             (result-handler new-e impurity scope))]
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
                  [impurity #f])
             (result-handler new-e impurity scope))]
          [`(define-values ,ids ,rhs)
           (let* ([new-rhs (traverse-subexpr rhs 0)]
                  [new-e `(define-values ,ids ,new-rhs)]
                  [impurity #t])
             (result-handler new-e impurity scope))]
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
                  [impurity (or (subexprs-impurity (map cadr new-clauses))
                                (subexprs-impurity new-body))])
             (result-handler new-e impurity scope))]
          [`(letrec-values ([,idss ,rhss] ...) ,bodys ...)
           (let* ([new-clauses
                   (for/list ([ids (in-list idss)]
                              [rhs (in-list rhss)]
                              [i (in-naturals)])
                     (list ids (traverse-subexpr rhs i)))]
                  [body-start (length new-clauses)]
                  [new-body (traverse-subexprs bodys body-start #t)]
                  [new-e `(letrec-values ,new-clauses ,@new-body)]
                  [impurity (or (subexprs-impurity (map cadr new-clauses))
                                (subexprs-impurity new-body))])
             (result-handler new-e impurity scope))]
          [`(if ,tst ,thn ,els)
           (let* ([new-tst (traverse-subexpr tst 0)]
                  [new-thn (traverse-subexpr thn 1)]
                  [new-els (traverse-subexpr els 2)]
                  [new-e `(if ,new-tst ,new-thn ,new-els)]
                  [impurity (subexprs-impurity (list new-tst new-thn new-els))])
             (result-handler new-e impurity scope))]
          [`(with-continuation-mark ,key ,val ,body)
           (let* ([new-key (traverse-subexpr key 0)]
                  [new-val (traverse-subexpr val 1)]
                  [new-body (traverse-subexpr body 2)]
                  [new-e `(with-continuation-mark ,new-key ,new-val ,new-body)]
                  [impurity (subexprs-impurity (list new-key new-val new-body))])
             (result-handler new-e impurity scope))]
          [`(begin ,exps ...)
           (let* ([new-body (traverse-subexprs exps 0 #t)]
                  [new-e `(begin ,@new-body)]
                  [impurity (subexprs-impurity new-body)])
             (result-handler new-e impurity scope))]
          [`(begin-unsafe ,exps ...)
           (let* ([new-body (traverse-subexprs exps 0 #t)]
                  [new-e `(begin-unsafe ,@new-body)]
                  [impurity (subexprs-impurity new-body)])
             (result-handler new-e impurity scope))]
          [`(begin0 ,exps ...)
           (let* ([new-body (traverse-subexprs exps 0 #t)]
                  [new-e `(begin0 ,@new-body)]
                  [impurity (subexprs-impurity new-body)])
             (result-handler new-e impurity scope))]
          [`(set! ,id ,rhs)
           (let* ([new-rhs (traverse-subexpr rhs 0)]
                  [new-e `(set! ,id ,new-rhs)]
                  [impurity #t])
             (result-handler new-e impurity scope))]
          [`(variable-reference-constant? ,_) e]
          [`(variable-reference-from-unsafe? ,_) e]
          [`(#%variable-reference . ,_) e]
          [`(,rator ,exps ...)
           (let* ([new-args (traverse-subexprs exps 0 #f)]
                  [new-e `(,rator ,@new-args)]
                  [impurity (subexprs-impurity new-args)])
             (result-handler new-e impurity scope))]
          [`,_ e])))

  ;; --------------------------------------------------------
  ;; Pass 1 handler: collect set!-mutated identifiers

  (define (collect-impure! e . _)
    (match e
      [`(set! ,id ,_) (hash-set! impure-ids (unwrap id) #t)]
      [`,_ (void)])
    e)

  ;; --------------------------------------------------------
  ;; Pass 2 handler: record expression/scope mappings

  (define (record-expr! expr impurity scp)
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
       (hash-set! sym-impure sym impurity)
       sym]))

  ;; --------------------------------------------------------
  ;; Build scp2dupsyms mapping

  (define (init-scp2dupsyms!)
    (for ([sym (in-hash-keys sym2scp)])
      (define scp (hash-ref sym2scp sym))
      (when (and (hash-has-key? sym-duplicate sym)
                 (not (hash-ref sym-impure sym #f)))
        (hash-set! scp2dupsyms scp
                   (cons sym (hash-ref scp2dupsyms scp '()))))))

  ;; --------------------------------------------------------
  ;; Pass 3 handler: reconstruct, inserting bindings for duplicates

  (define (reconstruct expr impurity scp)
    (define dupsyms (hash-ref scp2dupsyms scp #f))
    (if (not dupsyms)
        expr
        (cond
          [(and (pair? scp) (seq-element? (lst-last scp)))
           (list
             `(define-values ,dupsyms
                (values ,@(for/list ([sym (in-list dupsyms)])
                            (hash-ref sym2expr sym))))
             expr)]
          [else
           `(let-values
              ,(for/list ([sym (in-list dupsyms)])
                 `((,sym) ,(hash-ref sym2expr sym)))
              ,expr)])))

  ;; --------------------------------------------------------
  ;; Run passes

  (define (deep-unwrap v)
    (cond
      [(pair? v) (cons (deep-unwrap (car v)) (deep-unwrap (cdr v)))]
      [else (let ([u (unwrap v)]) (if (pair? u) (deep-unwrap u) u))]))

  (log-error (format "cse input: ~s" (deep-unwrap form)))

  (traverse-expr! form '() collect-impure!)
  (traverse-expr! form '() record-expr!)
  (init-scp2dupsyms!)
  (define res (traverse-expr! form '() reconstruct))

  (log-error (format "cse result: ~s" (deep-unwrap res)))
  form

  )
