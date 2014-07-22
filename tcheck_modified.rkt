#lang racket
(require "pmatch.rkt")
(provide typecheck)
(provide consistent?)
(provide meet)

;All functions taken from:

;Siek, J. G., & Garcia, R. (2013). 
;Interpretations of the Gradually-Typed Lambda Calculus. 
;Proceedings of the Scheme and Functional Programming Workshop.
;Retrieved from http://wphomes.soic.indiana.edu/jsiek/files/2013/06/igtlc.pdf


;Returns true if one type can be casted to another
(define consistent?
  (lambda (FT1 FT2)   
    (pmatch `(,FT1 ,FT2)
            (`(,FT1 dyn) #t)
            (`(dyn ,FT2) #t)
            (`(int int) #t)
            (`(bool bool) #t)
            (`((-> ,FT11 ,FT12) (-> ,FT21 ,FT22)) 
             (and (consistent? FT12 FT22) (consistent? FT11 FT21)))
            (`,other #f))))

;Returns the most specific combination of two consistent types, displays blame label if fail
(define meet
  (lambda (TT1 TT2 [blame `(,TT1 ,TT2)]) 
    (pmatch `(,TT1 ,TT2)
            (`(,TT1 dyn) TT1)
            (`(dyn ,TT2) TT2)
            (`(int int) `int)
            (`(bool bool) `bool)
            (`((-> ,TT11 ,TT12) (-> ,TT21 ,TT22)) 
             `(-> ,(meet TT11 TT21) ,(meet TT12 TT22)))
            (`other (error 'meet "types are not consistent, blame: " blame)))))

;Returns true if k is int or bool
(define constant?
  (lambda (k)
    (or (integer? k) (boolean? k))))

;Returns true if op is inc, dec, or zero?
(define operator?
  (lambda (op)
    (memq op '(inc dec zero?))))

;Returns type of constant or operator function
(define typeof
  (lambda (k)
    (pmatch k
            (`,n (guard (integer? n)) `int)
            (`,b (guard (boolean? b)) `bool)
            (`inc `(-> int int))
            (`dec `(-> int int))
            (`zero? `(-> int bool)))))

;If two types are different type1 is casted to type2
(define mk-cast
  (lambda (l e T1 T2)
    (cond ((equal? T1 T2) e)
          (else 
           (pmatch `(,T1 ,T2)
                   (`((-> ,T3 ,T4) dyn) 
                   `(cast ,l (cast ,l ,e : ,T1 -> (-> dyn dyn)) : (-> dyn dyn) -> ,T2))
                   (`(dyn (-> ,T3 ,T4))
                    `(cast ,l (cast ,l ,e : dyn -> (-> dyn dyn)) : (-> dyn dyn) -> ,T2))
                    (`(,T3 ,T4)                 
                   
                   `(cast ,l ,e : ,T1 -> ,T2)))))))


;Typehecks a program in the gradually-typed lambda calculus
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
                     (`((,new-cnd ,cnd-T) (,new-thn ,thn-T) (,new-els ,els-T))                      
                      (cond
                        ((and (consistent? thn-T els-T) (consistent? cnd-T `bool))
                         (let ((if-T (meet thn-T els-T)))                                                                                    
                           `((if ,(mk-cast l new-cnd cnd-T `bool) 
                                 ,(mk-cast l new-thn thn-T if-T) 
                                 ,(mk-cast l new-els els-T if-T)) ,if-T)))                        
                        (else (error 'typecheck "ill-typed expression"))))))
            (`,x (guard (symbol? x)) `(,x ,(car (cdr (assq x env)))))
            (`(lambda (,x) ,e1) (typecheck env `(lambda (,x : dyn) ,e1)))
            (`(lambda (,x : ,T1) ,e1)
             (pmatch `,(typecheck `((,x ,T1) . ,env) e1)
                     (`(,new-e ,ret-T) `((lambda (,x : ,T1) ,new-e)(-> ,T1 ,ret-T)))))
            (`(,e1 : ,T ,l)
             (pmatch `,(typecheck env e1)
                     (`(,new-e ,e-T)
                      (cond
                        ((consistent? e-T T) `(,(mk-cast l new-e e-T T) ,T))                        
                        (else (error 'typecheck "cast between inconsistent types"))))))            
            (`(,e1 ,e2 ,l)             
             (pmatch `( ,(typecheck env e2) ,(typecheck env e1))
                     (`((,new-e2 ,T2) (,new-e1 dyn))                     
                      `((call ,(mk-cast l new-e1 `dyn `(-> ,T2 dyn)) ,new-e2) dyn))
                     (`((,new-e2 ,T2) (,new-e1 (-> ,T11 ,T12)))
                      (cond
                        ((consistent? T2 T11)
                         `((call ,new-e1 ,(mk-cast l new-e2 T2 T11)) ,T12))
                        (else (error 'typecheck "arg/param mismatch" T2 T11))))
                     (`((,new-e2 ,T2) (,new-e1 ,other-T))                   
                      (error 'typecheck "call to non-function")))))))

