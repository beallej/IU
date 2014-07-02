#lang racket
(require "pmatch.rkt")
(provide typecheck)
(define consistent?
  (lambda (FT1 FT2)
   
    (pmatch `(,FT1 ,FT2)
            (`(,FT1 dyn) #t)
            (`(dyn ,FT2) #t)
            (`(int int) #t)
            (`(bool bool) #t)
            (`((-> ,FT11 ,FT12) (-> ,FT21 ,FT22)) (and (consistent? FT12 FT22) (consistent? FT11 FT21)))
            (`other #f))))
(define meet
  (lambda (TT1 TT2) 
    (pmatch `(,TT1 ,TT2)
            (`(,TT1 dyn) TT1)
            (`(dyn ,TT2) TT2)
            (`(int int) `int)
            (`(bool bool) `bool)
            (`((-> ,TT11 ,TT12) (-> ,TT21 ,TT22)) `(-> ,(meet TT11 TT21) ,(meet TT12 TT22)))
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
            (`,n (guard (integer? n)) `int)
            (`,b (guard (boolean? b)) `bool)
            (`inc `(-> int int))
            (`dec `(-> int int))
            (`zero? `(-> int bool)))))


(define mk-cast
  (lambda (l e T1 T2)
    (cond ((equal? T1 T2) e)
          (else `(cast ,l ,e : ,T1 -> ,T2)))))
;(define infer
;  (lambda (env e)
;    (pmatch e
;         (`,k (guard (constant? k)) `k)
;            (`(,op ,e1 ,l) (guard (operator? op))
;                           (pmatch `(,(typecheck env e1) ,(typeof op))
;                                   (`((,new-e ,T) (-> ,T1 ,T2)) (guard (consistent? T T1))
;                                                                `(,op ,e1 ,l))
;                                   (`,other (error 'typecheck "primitive operator"))))
;            (`(if ,cnd ,thn ,els ,l)
;             (pmatch `(,(typecheck env cnd) ,(typecheck env thn) ,(typecheck env els))
;                     (`((,new-cnd ,cnd-T) (,new-thn ,thn-T) (,new-els ,els-T)) (cond
;                                                                                 ((and (consistent? thn-T els-T) (consistent? cnd-T 'bool))
;                                                                                  (let ((if-T (meet thn-T els-T)))
;                                                                                    `((if ,(mk-cast l new-cnd cnd-T `bool) ,(mk-cast l new-thn thn-T if-T) ,(mk-cast l new-thn els-T if-T)) ,if-T)))
;                                                                                 (else (error 'typecheck "ill-typed expression"))))))
;            (`,x (guard (symbol? x)) `(,x ,(cdr (assq x env))))
;            (`(lambda (,x) ,e1) (typecheck env `(lambda (,x : dyn) ,e1)))
;            (`(lambda (,x : ,T1) ,e1)
;             (pmatch `,(typecheck `((,x . ,T1) . ,env) e1)
;                     (`(,new-e ,ret-T) `((lambda (,x : ,T1) ,new-e)(-> ,T1 ,ret-T)))))
;            (`(,e1 : ,T ,l)
;             (pmatch `(typecheck env e1)
;                     (`(,new-e ,e-T)
;                      (cond
;                        ((consistent? e-T T) `(,(mk-cast l new-e e-T T)))
;                        (else (error 'typecheck "cast between inconsistent types"))))))
;            (`(,e1 ,e2 ,l)
;             (pmatch `( ,(typecheck env e2) ,(typecheck env e1))
;                     (`((,new-e2 ,T2) (,new-e1 dyn))
;                      `((call ,(mk-cast l new-e1 `dyn `(-> ,T2 dyn)) ,new-e2) dyn))
;                     (`((,new-e2 ,T2) (,new-e1 (-> ,T11 ,T12)))
;                      (cond
;                        ((consistent? T2 T11) `((call ,new-e1 ,(mk-cast l new-e2 T2 T11)) ,T12))
;                        (else (error 'typecheck "arg/param mismatch"))))
;                     (`((,new-e2 ,T2) (,new-e1 ,other-T))
;                      (error 'typecheck "call to non-function" )))))))   
;            
            
            
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
                                                                                 ((and (consistent? thn-T els-T) (consistent? cnd-T `bool))
                                                                                  (let ((if-T (meet thn-T els-T)))                                                                                    
                                                                                    `((if ,(mk-cast l new-cnd cnd-T `bool) ,(mk-cast l new-thn thn-T if-T) ,(mk-cast l new-els els-T if-T)) ,if-T)))
                                                                                 ;NOTE: (mk-cast l new-els els-T if-T) WAS ORIGINALLY (mk-cast l new-thn els-T if-T), but i changed that because
                                                                                 ;i think it was a mistake
                                                                                 (else (error 'typecheck "ill-typed expression"))))))
            (`,x (guard (symbol? x)) `(,x ,(car (cdr (cdr (assq x env))))))
            (`(lambda (,x ,id) ,e1) (typecheck env `(lambda (,x ,id : dyn) ,e1)))
            (`(lambda (,x ,id : ,T1) ,e1)
             (pmatch `,(typecheck `((,x ,id ,T1) . ,env) e1)
                     (`(,new-e ,ret-T) `((lambda (,x ,id : ,T1) ,new-e)(-> ,T1 ,ret-T)))))
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