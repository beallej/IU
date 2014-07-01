#lang racket
(require "pmatch.rkt")
(define consistent?
  (lambda (T1 T2)
    (pmatch `(,T1 ,T2)
            (`(,T1 dyn) #t)
            (`(dyn ,T2) #t)
            (`(int int) #t)
            (`(bool bool) #t)
            (`((-> ,T11 ,T12) (-> ,T21 ,T22)) (and (consistent? T12 T22) (consistent? T11 T21)))
            (`other #f))))
(define meet
  (lambda (T1 T2)
    (pmatch `(,T1 ,T2)
            (`(,T1 dyn) T1)
            (`(dyn ,T2) T2)
            (`(int int) 'int)
            (`(bool bool) 'bool)
            (`((-> ,T11 ,T12) (-> ,T21 ,T22)) (-> (meet T11 T21) (meet T12 T22)))
            (`other (error 'meet "types are not consistent")))))
(define cast
  (lambda (l e T1 T2)
    (if (consistent? T1 T2)
        #t #f)))
(define prim
  (lambda (op e)
    #t))
(define call
  (lambda (e1 e2)
    #t))
(define constant?
  (lambda (k)
    (or (integer? k) (boolean? k))))
(define operator?
  (lambda (op)
    (memq op '(inc dec zero?))))
(define typeof
  (lambda (k)
    (pmatch k
            (`,n (guard (integer? n)) 'int)
            (`,b (guard (boolean? b)) 'bool)
            (`inc '(-> int int))
            (`dec '(-> int int))
            (`zero? '(-> int bool)))))

(define mk-cast
  (lambda (l e T1 T2)
    (cond ((equal? T1 T2) e)
          (else `(cast ,l ,e : ,T1 -> ,T2)))))
(define infer
  (lambda (env e)
    (pmatch e
         (`,k (guard (constant? k)) `k)
            (`(,op ,e1 ,l) (guard (operator? op))
                           (pmatch `(,(typecheck env e1) ,(typeof op))
                                   (`((,new-e ,T) (-> ,T1 ,T2)) (guard (consistent? T T1))
                                                                `(,op ,e1 ,l))
                                   (`,other (error 'typecheck "primitive operator"))))
            (`(if ,cnd ,thn ,els ,l)
             (pmatch `(,(typecheck env cnd) ,(typecheck env thn) ,(typecheck env els))
                     (`((,new-cnd ,cnd-T) (,new-thn ,thn-T) (,new-els ,els-T)) (cond
                                                                                 ((and (consistent? thn-T els-T) (consistent? cnd-T 'bool))
                                                                                  (let ((if-T (meet thn-T els-T)))
                                                                                    `((if ,(mk-cast l new-cnd cnd-T 'bool) ,(mk-cast l new-thn thn-T if-T) ,(mk-cast l new-thn els-T if-T)) ,if-T)))
                                                                                 (else (error 'typecheck "ill-typed expression"))))))
            (`,x (guard (symbol? x)) `(,x ,(cdr (assq x env))))
            (`(λ (,x) ,e1) (typecheck env `(λ (,x : dyn) ,e1)))
            (`(λ (,x : ,T1) ,e1)
             (pmatch `,(typecheck `((,x . ,T1) . ,env) e1)
                     (`(,new-e ,ret-T) `((λ (,x : ,T1) ,new-e)(-> ,T1 ,ret-T)))))
            (`(,e1 : ,T ,l)
             (pmatch `(typecheck env e1)
                     (`(,new-e ,e-T)
                      (cond
                        ((consistent? e-T T) `(,(mk-cast l new-e e-T T)))
                        (else (error 'typecheck "cast between inconsistent types"))))))
            (`(,e1 ,e2 ,l)
             (pmatch `( ,(typecheck env e2) ,(typecheck env e1))
                     (`((,new-e2 ,T2) (,new-e1 dyn))
                      `((call ,(mk-cast l new-e1 `dyn `(-> ,T2 dyn)) ,new-e2) dyn))
                     (`((,new-e2 ,T2) (,new-e1 (-> ,T11 ,T12)))
                      (cond
                        ((consistent? T2 T11) `((call ,new-e1 ,(mk-cast l new-e2 T2 T11)) ,T12))
                        (else (error 'typecheck "arg/param mismatch"))))
                     (`((,new-e2 ,T2) (,new-e1 ,other-T))
                      (error 'typecheck "call to non-function")))))))   
            
            
            
(define typecheck
  (lambda (env e)
    (pmatch e
            (`,k (guard (constant? k)) `(,k ,(typeof k)))
            (`(,op ,e1 ,l) (guard (operator? op))
                           (pmatch `(,(typecheck env e1) ,(typeof op))
                                   (`((,new-e ,T) (-> ,T1 ,T2)) (guard (consistent? T T1))
                                                                `((prim ,op ,(mk-cast l new-e T T1)) ,T2))
                                   (`,other (error 'typecheck "primitive operator"))))
            (`(if ,cnd ,thn ,els ,l)
             (pmatch `(,(typecheck env cnd) ,(typecheck env thn) ,(typecheck env els))
                     (`((,new-cnd ,cnd-T) (,new-thn ,thn-T) (,new-els ,els-T)) (cond
                                                                                 ((and (consistent? thn-T els-T) (consistent? cnd-T 'bool))
                                                                                  (let ((if-T (meet thn-T els-T)))
                                                                                    `((if ,(mk-cast l new-cnd cnd-T 'bool) ,(mk-cast l new-thn thn-T if-T) ,(mk-cast l new-thn els-T if-T)) ,if-T)))
                                                                                 (else (error 'typecheck "ill-typed expression"))))))
            (`,x (guard (symbol? x)) `(,x ,(cdr (assq x env))))
            (`(λ (,x) ,e1) (typecheck env `(λ (,x : dyn) ,e1)))
            (`(λ (,x : ,T1) ,e1)
             (pmatch `,(typecheck `((,x . ,T1) . ,env) e1)
                     (`(,new-e ,ret-T) `((λ (,x : ,T1) ,new-e)(-> ,T1 ,ret-T)))))
            (`(,e1 : ,T ,l)
             (pmatch `(typecheck env e1)
                     (`(,new-e ,e-T)
                      (cond
                        ((consistent? e-T T) `(,(mk-cast l new-e e-T T)))
                        (else (error 'typecheck "cast between inconsistent types"))))))
            (`(,e1 ,e2 ,l)
             (pmatch `( ,(typecheck env e2) ,(typecheck env e1))
                     (`((,new-e2 ,T2) (,new-e1 dyn))
                      `((call ,(mk-cast l new-e1 `dyn `(-> ,T2 dyn)) ,new-e2) dyn))
                     (`((,new-e2 ,T2) (,new-e1 (-> ,T11 ,T12)))
                      (cond
                        ((consistent? T2 T11) `((call ,new-e1 ,(mk-cast l new-e2 T2 T11)) ,T12))
                        (else (error 'typecheck "arg/param mismatch"))))
                     (`((,new-e2 ,T2) (,new-e1 ,other-T))
                      (error 'typecheck "call to non-function")))))))