#lang racket/base

(let ([x 1])
  (+ (let ([y 2]) (+ (+ (+ y 1) (+ y 1)) (+ x 2)))
     (let ([z 3]) (+ z (+ x 2)))))