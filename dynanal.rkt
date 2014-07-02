#lang racket
(require  "pmatch.rkt")
(require racket/include)
(require "tcheck_modified.rkt")
(require racket/contract)
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
            (`,num (guard (number? num)) `int)
            (`,bool (guard (boolean? bool)) `bool)
            (`(inc ,x ,L) `int)
            (`(dec ,x ,L) `int)
            (`(zero? ,x ,L) `bool)
            (`(closure ,x ,id ,e ,env) `(-> (type ,id) (type ,e))))))
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
               ;(display "newtype: ")
               ;(display newtype)
               ;(display "\n")
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
                                      ;(pmatch v2
                                              ;(`(closure ,y ,id12 ,e12 ,env12)
                                               ;(set! type-obs (extend-Trec id (type v2) type-obs))                                               
                                              ; (evalRec `(,v2 ,e11) (extend-env x id v2 env11)))
                                             ; (`,else
                                               (set! type-obs (extend-Trec id (type v2) type-obs))                                               
                                               (evalRec e11 (extend-env x id v2 env11))))));))                                     
            
            ;(`((closure ,y ,id12 ,e12 ,env12) ,e) ???)
            (`(,e : ,T ,l)
             `(cast ,l ,e ,T))
            ;(set! type-obs (extend-Trec id T type-obs))
            ;(set! type-obs (extend-Trec (env-lookup-id x env) T type-obs))
            
            (`(cast ,l ,e ,T)  ;WHAT DO I DO WITH CASTS???
             (set! type-obs (extend-Trec (gensym) T type-obs))
             (evalRec e env))
            ;(`,x (let ((ans (env-lookup x env)) (tp (env-lookup-id x env))) (set! type-obs (extend-Trec tp (type ans) type-obs)) ans)))))
            (`,x (let ((ans (env-lookup x env)) (tp (env-lookup-id x env)))  ans)))));(set! type-obs (extend-Trec tp (env-lookupT tp type-obs) type-obs)) ;ans)))))
            ;(`,x (env-lookup x env)))))
(define extend-env
  (lambda (x id y env)
    `(,(list x id y) . ,env)))    

(define extend-Trec
  (lambda (x T env) 
    ;(display env)
    ;(display "   8  \n")
    (if (null? env) `(,(cons x (list (list T))))
        (if (equal? x (car (car env)))         
            `,(cons 
               (cons x
                     (cond
                       [(null? (cdr (car env)))`( ,(cons T (cdr (car env))))]
                       [(member T (car (cdr (car env)))) `,(cdr (car env))]
                       [else (list (append (list T) (cdr (car env))))]))
               
               ;                      (if 
               ;                       (member T (car (cdr env))) 
               ;                       (car (cdr env)) 
               ;                       (cons T (car (cdr env)))))
               (cdr env))
            `,(cons (car env) (extend-Trec x T (cdr env)))))))
(define env-lookup-id
  (lambda (x env)
    (let ((info (assoc x env))) 
      (if info (car (cdr info)) (error "id- unbound variable" x)))))
(define env-lookup
  (lambda (x env)
    (let ((info (assoc x env)))
      (if info (car (cdr (cdr info))) (error "unbound variable" x)))))
(define env-lookupT
  (lambda (id env)
    (let ((info (assoc id env)))
      (if info
          (check-consistency (cdr (cdr info)) (resolve-type (car (car (cdr info)))))
          'null))))
;    (if (null? env) 'null
;        (if (equal? id (car (car env)))
;            (check-consistency (cdr (cdr (car env))) (car (cdr (car env))))
;            (env-lookupT id (cdr env))))))
(define check-consistency
  (lambda (types type1)
    (if (null? types) type1
    (let ((type2 (resolve-type (car types))))
    (cond    
      [(equal? type1 'dyn) (check-consistency (cdr types) type2)]
      [(equal? type2 'dyn) (check-consistency (cdr types) type1)]
      [(equal? type1 type2) (check-consistency (cdr types) type1)]
      [else (error "types inconsistent" type1"   " (car types))])))))


(define resolve-type
  (lambda (tv)
    (pmatch tv
            (`int `int)
            (`bool `bool)
            (`(-> ,t1 ,t2) `(-> ,(resolve-type t1) ,(resolve-type t2)))
            (`(type (,op ,e ,L)) (guard (member op '(inc dec))) `int) ;WHAT TO DO WITH E??
            (`(type (zero? ,e ,L)) `bool)
            (`(type ,id) (let ((typed (env-lookupT id type-obs))) (if (equal? null typed) `dyn typed))))))
            


;(evals '((lambda (d d6) (zero? d L)) 
;           9 
;           L))
(evals '((lambda (c c5) (if c (lambda (v v7) (dec v L)) (lambda (w w8) (inc w L)) L)) 
          #t 
          L))
(evals '(((lambda (c c5) (if c (lambda (v v7) (dec v L)) (lambda (w w8) (inc w L)) L)) 
          #t 
          L)
         7 
         L))
(evals '(((lambda (c c5) (if c (lambda (v v7) (dec v L)) (lambda (w w8) (inc w L)) L)) 
          ((lambda (d d6) (zero? d L)) 
           9 
           L) 
          L) 7 L))
(evals '((lambda (b b4) (b 7 L)) 
         ((lambda (c c5) (if c (lambda (v v7) (dec v L)) (lambda (w w8) (inc w L)) L )) 
          ((lambda (d d6) (zero? d L)) 
           9 
           L) 
          L)
         L))                 
(evals '(lambda (m m12) (m 3 L)))
(evals '((lambda (g g12) ((lambda (h h12) ((lambda (i i12) (if i g h L)) #t L)) 4 L)) 9 L))
(evals '((lambda (j j12) (j 3 L)) (lambda (q q12) (inc q L)) L))
(evals '((lambda (j j12) (j 3 L)) (lambda (q q12) (dec q L)) L))
(evals '((lambda (x x14) (inc x L)) 3 L))
(evals '((lambda (x x12) (if x 7 8 L)) #t L))
;(evals '((lambda (x x12) (if x 7 #f L)) #f L))
;(evals '((lambda (y y12) (if #t y 7 L)) #t L))
;(evals '((lambda (y y12) (if #t y 7 L)) 9 L))
(set! type-obs '())