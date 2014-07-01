#lang racket
(require  "pmatch.rkt")
(require racket/include)
(require "tcheck_modified.rkt")
(define type-obs
  '())

(define evals
  (lambda (exp)
    (display "Original expression: ")
    (display exp)
    (display "\nEvaluation: ")
    (display (evalRec exp '()))
    (display "\nType Observations: ")
    (display type-obs)
    (display "\nTypes Inserted: ")
    (display (insert-types exp))
    (display "\nOriginal check: ")
    (display (typecheck '() exp))
    (display "\nCheck with new types: ")
    (display (typecheck '() (insert-types exp)))
    (display "\n")
    (display "\n")))
(define type
  (lambda (exp)
    (pmatch exp
            (`,num (guard (number? num)) 'int)
            (`,bool (guard (boolean? bool)) 'bool)
            (`(inc ,x) `(-> int int))
            (`(dec ,x) `(-> int int))
            (`(zero? ,x) `(-> int bool))
            (`(closure ,x ,id ,e ,env) `(-> dyn dyn)))))
;(define insert-types
;  (lambda (exp)     
;    (pmatch exp           
;            (`,num (guard (number? num)) num)
;            (`,bool (guard (boolean? bool)) bool)
;            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
;                          `(,op ,(insert-types e) ,l))
;            (`(if ,t ,c ,a ,l) 
;             `(if ,(insert-types t) ,(insert-types c) ,(insert-types a) ,l))
;            (`(lambda (,x ,id : ,T) ,e)     
;             `(lambda (,x ,id : ,(env-lookupT id type-obs)) ,e))    
;            (`(lambda (,x ,id) ,e)
;             (let ((newtype (env-lookupT id type-obs)))
;               (if (equal? newtype 'null)
;                   `(lambda (,x ,id) ,(insert-types e))
;                   `(lambda (,x ,id : ,newtype) ,(insert-types e)))))
;            (`(,e1 ,e2 ,l)             
;             `(,(insert-types e1) ,(insert-types e2) ,l)) 
;            (`(,e ,id : ,T ,l)     
;                                  ;`(,e ,id : ,(env-lookupT id type-obs))) 
;             `(,(insert-types e) ,id : ,(env-lookupT id type-obs)))
;            (`,x `,x))))
(define insert-types
  (lambda (exp)     
    (pmatch exp           
            (`,num (guard (number? num)) num)
            (`,bool (guard (boolean? bool)) bool)
            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
                          `(,op ,(insert-types e) ,l))
            (`(if ,t ,c ,a ,l) 
             `(if ,(insert-types t) ,(insert-types c) ,(insert-types a) ,l))
            (`(lambda (,x ,id : ,T) ,e)     
             `(lambda (,x ,id : ,(env-lookupT id type-obs)) ,e))    
            (`(lambda (,x ,id) ,e)
             (let ((newtype (env-lookupT id type-obs)))
               (if (equal? newtype 'null)
                   `(lambda (,x ,id) ,(insert-types e))
                   `(lambda (,x ,id : ,newtype) ,(insert-types e)))))
            (`(,e1 ,e2 ,l)             
             `(,(insert-types e1) ,(insert-types e2) ,l)) 
            (`(,e ,id : ,T ,l)     
             ;`(,e ,id : ,(env-lookupT id type-obs))) 
             `(,(insert-types e) ,id : ,(env-lookupT id type-obs)))
            (`(,e : ,T ,l)     
             ;`(,e ,id : ,(env-lookupT id type-obs))) 
             `(,(insert-types e) : ,T ,l))
            (`,x `,x))))











(define evalRec
  (lambda (exp env)
    (pmatch exp
            (`,num (guard (number? num)) num)
            ;(`(,num ,id) (guard (number? num)) (set! type-obs (extend-Trec id 'int type-obs)) num)
            (`,bool (guard (boolean? bool)) bool)
            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
                          (let ((nexp (evalRec e env)))
                            (cond
                              ((not (number? nexp)) (error "expression not number, problem is " l))
                              ((eq? 'inc op) (+ 1 nexp))
                              ((eq? 'dec op) (- nexp 1))
                              ((eq? 'zero? op) (zero? nexp)))))
            (`(if ,t ,c ,a ,l) (let ((texp (evalRec t env)))
                                 (if  (boolean? texp)
                                      (if texp
                                          (evalRec c env)
                                          (evalRec a env))
                                      (error "test not boolean, problem is: " l))))
            (`(lambda (,x ,id : ,T) ,e)
             ;(let ((id (gensym x)))
             (set! type-obs (extend-Trec id T type-obs))
             `(closure ,x ,id ,e ,env));)
            
            (`(lambda (,x ,id) ,e)
             ;`(closure ,x ,(gensym x) ,e ,env))
             `(closure ,x ,id ,e ,env))
            
            
            (`(,e1 ,e2 ,l) (let* ([v1 (evalRec e1 env)] [v2 (evalRec e2 env)])
                             (pmatch v1                                    
                                     (`(closure ,x ,id ,e11 ,env11)
                                      (pmatch v2
                                              (`(closure ,y ,id12 ,e12 ,env12)
                                               (set! type-obs (extend-Trec id (type v2) type-obs))                                               
                                               (evalRec `(,v2 ,e11) (extend-env x id v2 env11)))
                                              (`,else
                                               (set! type-obs (extend-Trec id (type v2) type-obs))                                               
                                               (evalRec e11 (extend-env x id v2 env11))))))))                                     
            
            (`((closure ,y ,id12 ,e12 ,env12) ,e) ???)
            (`(,e : ,T ,l)
             `(cast ,l ,e ,T))
            ;(set! type-obs (extend-Trec id T type-obs))
            ;(set! type-obs (extend-Trec (env-lookup-id x env) T type-obs))
            
            (`(cast ,l ,e ,T)  ;WHAT DO I DO WITH CASTS???
             (set! type-obs (extend-Trec (gensym) T type-obs))
             (evalRec e env))
            
            (`,x (env-lookup x env)))))
(define extend-env
  (lambda (x id y env)
    `(,(list x id y) . ,env)))    

(define extend-Trec
  (lambda (x T env)    
    (if (null? env) `(,(cons x `((,T))))
        (if (equal? x (car (car env)))         
            `,(cons 
               (cons x
                     (cond
                       [(null? (cdr (car env)))`( ,(cons T (cdr (car env))))]
                       [(member T (car (cdr (car env)))) `,(car (cdr (car env)))]
                       [else (cons T (car (cdr (car env))))]))
               
               ;                      (if 
               ;                       (member T (car (cdr env))) 
               ;                       (car (cdr env)) 
               ;                       (cons T (car (cdr env)))))
               (cdr env))
            `,(cons (car env) (extend-Trec x T (cdr env)))))))
;(define env-lookup-id
;  (lambda (x env)
;    (let ((info (assoc x env))) 
;      (if info (car (cdr info)) (error "id- unbound variable" x)))))
(define env-lookup
  (lambda (x env)
    (let ((info (assoc x env)))
      (if info (car (cdr (cdr info))) (error "unbound variable" x)))))
(define env-lookupT
  (lambda (id env)
    (let ((info (assoc id env)))
      
      (if info
          (check-consistency (cdr (cdr info)) (car (car (cdr info))))
          'null))))
;    (if (null? env) 'null
;        (if (equal? id (car (car env)))
;            (check-consistency (cdr (cdr (car env))) (car (cdr (car env))))
;            (env-lookupT id (cdr env))))))
(define check-consistency
  (lambda (types type1)
    
    (cond
      [(null? types) type1]
      [(equal? type1 'dyn) (check-consistency (cdr types) (car types))]
      [(equal? (car types) 'dyn) (check-consistency (cdr types) type1)]
      [(equal? type1 (car types)) (check-consistency (cdr types) type1)]
      [else (error "types inconsistent")])))













;(define consistent?
;  (lambda (T1 T2)
;    (pmatch `(,T1 ,T2)
;            (`(,T1 dyn) #t)
;            (`(dyn ,T2) #t)
;            (`(int int) #t)
;            (`(bool bool) #t)
;            (`((-> ,T11 ,T12) (-> ,T21 ,T22)) (and (consistent? T12 T22) (consistent? T11 T21)))
;            (`other #f))))
;(define meet
;  (lambda (T1 T2)
;    (pmatch `(,T1 ,T2)
;            (`(,T1 dyn) T1)
;            (`(dyn ,T2) T2)
;            (`(int int) 'int)
;            (`(bool bool) 'bool)
;            (`((-> ,T11 ,T12) (-> ,T21 ,T22)) (-> (meet T11 T21) (meet T12 T22)))
;            (`other (error 'meet "types are not consistent")))))
;(define cast
;  (lambda (l e T1 T2)
;    (if (consistent? T1 T2)
;        #t #f)))
;(define prim
;  (lambda (op e)
;    #t))
;(define call
;  (lambda (e1 e2)
;    #t))
;(define constant?
;  (lambda (k)
;    (or (integer? k) (boolean? k))))
;(define operator?
;  (lambda (op)
;    (memq op '(inc dec zero?))))
;(define typeof
;  (lambda (k)
;    (pmatch k
;            (`,n (guard (integer? n)) 'int)
;            (`,b (guard (boolean? b)) 'bool)
;            (`inc '(-> int int))
;            (`dec '(-> int int))
;            (`zero? '(-> int bool)))))
;
;(define mk-cast
;  (lambda (l e T1 T2)
;    (cond ((equal? T1 T2) e)
;          (else `(cast ,l ,e : ,T1 -> ,T2)))))
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
;                                                                                    `((if ,(mk-cast l new-cnd cnd-T 'bool) ,(mk-cast l new-thn thn-T if-T) ,(mk-cast l new-thn els-T if-T)) ,if-T)))
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
;                      (error 'typecheck "call to non-function")))))))   
;            
;            
;            
;(define typecheck
;  (lambda (env e)
;    (pmatch e
;            (`,k (guard (constant? k)) `(,k ,(typeof k)))
;            (`(,op ,e1 ,l) (guard (operator? op))
;                           (pmatch `(,(typecheck env e1) ,(typeof op))
;                                   (`((,new-e ,T) (-> ,T1 ,T2)) (guard (consistent? T T1))
;                                                                `((prim ,op ,(mk-cast l new-e T T1)) ,T2))
;                                   (`,other (error 'typecheck "primitive operator"))))
;            (`(if ,cnd ,thn ,els ,l)
;             (pmatch `(,(typecheck env cnd) ,(typecheck env thn) ,(typecheck env els))
;                     (`((,new-cnd ,cnd-T) (,new-thn ,thn-T) (,new-els ,els-T)) (cond
;                                                                                 ((and (consistent? thn-T els-T) (consistent? cnd-T 'bool))
;                                                                                  (let ((if-T (meet thn-T els-T)))
;                                                                                    `((if ,(mk-cast l new-cnd cnd-T 'bool) ,(mk-cast l new-thn thn-T if-T) ,(mk-cast l new-thn els-T if-T)) ,if-T)))
;                                                                                  (else (error 'typecheck "ill-typed expression"))))))
;            (`(,x ,id) (guard (symbol? x)) `(,x ,(cdr (assq id env))))
;            (`,x (guard (symbol? x)) `(,x ,(cdr (assq id env))))
;            (`(lambda (,x ,id) ,e1) (typecheck env `(lambda (,x ,id : dyn) ,e1)))
;            (`(lambda (,x ,id : ,T1) ,e1)
;             (pmatch `,(typecheck `((,x ,id ,T1) . ,env) e1)
;                     (`(,new-e ,ret-T) `((lambda (,x ,id : ,T1) ,new-e)(-> ,T1 ,ret-T)))))
;            (`(,e1 ,id : ,T ,l)
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
;                      (error 'typecheck "call to non-function")))))))

(evals '((lambda (g g12) ((lambda (h h12) ((lambda (i i12) (if i g h L)) #t L)) 4 L)) 9 L))
(evals '((lambda (j j12) (j 3 L)) (lambda (q q12) (inc q L)) L))
(evals '((lambda (x x14) (inc x L)) 3 L))
(evals '((lambda (x x12) (if x 7 8 L)) #t L))
;(evals '((lambda (x x12) (if x 7 #f L)) #f L))
;(evals '((lambda (y y12) (if #t y 7 L)) #t L))
;(evals '((lambda (y y12) (if #t y 7 L)) 9 L))
(set! type-obs '())