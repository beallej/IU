#lang racket
(require  "pmatch.rkt")
(require racket/include)
(require "tcheck_modified.rkt")
(require test-engine/racket-tests)


;Original type observation global list
(define type-obs
  (hash))
;Original coverage stack
(define cov
  '())
;Performs dynamic analysis and prints out results
(define evals
  (lambda (exp)
    (display "Original expression: \n")
    (display exp)
    ;(set! exp (uniquify exp))
    (display "\n\nEvaluation: \n")
    (display (evalRec exp '()))
    (display "\n\nCoverage: \n")
    (display (cov-pc))
    (display "%")
    (display "\n\nType Observations: \n")
    (display type-obs)
    (display "\n\nTypes Inserted: \n")
    (display (insert-types exp))
    (display "\n\nOriginal check: \n")
    (display (typecheck '() exp))
    (display "\n\nCheck with new types: \n")
    (display (typecheck '() (insert-types exp)))
    (display "\n\n--------------------------------------------\n")      
    (set! cov '())))

(define unique
  (lambda (exp)
    (vary exp (hash))))
(define vary
  (lambda (exp env)
    (pmatch exp
            (`,num (guard (number? num)) num)
            (`,bool (guard (boolean? bool)) bool)
            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
                          `(,op ,(vary e env) ,l))
            (`(if ,t ,c ,a ,l) 
             `(if ,(vary t env) ,(vary c env) ,(vary a env) ,l))
            (`(lambda (,x : ,T) ,e)
             (let ((xid (gensym x)))
               `(lambda (,xid : ,T) ,(vary e (hash-set env x xid)))))                 
            (`(lambda (,x) ,e)
             (let ((xid (gensym x)))
               `(lambda (,xid) ,(vary e (hash-set env x xid))))) 
            (`(,e1 ,e2 ,l)             
             `(,(vary e1 env) ,(vary e2 env) ,l))             
            (`(,e : ,T ,l)              
             `(,(vary e env) : ,T ,l))
            (`,x `,(hash-ref env x (lambda () (error 'type-of "unbound id: ~a not found in ~a" x env)))))))
    
;Calculates coverage percent
(define cov-pc
  (lambda ()
    (let ((dec (calc-cov))) 
      (if (null? dec) 0
          (/ (round (* 10000.0 dec)) 100)))))

;Calculates coverage
;pop and push car, it is the number of sub expressions.
;pop, push, recur on next "car" subexpressions
;if stack empty, it is because it is missing 0's from a true if statement.          
(define calc-cov
  (lambda ()    
    (if (null? cov) 0
        (let ((front (car cov)))
          (set! cov (cdr cov))
          (cond
            [(eq? '3 front) (+ (* 1/3 (calc-cov)) (* 1/3 (calc-cov)) (* 1/3 (calc-cov)))]
            [(eq? '2 front) (+ (* 1/3 (calc-cov)) (* 1/3 (calc-cov)))]
            [(eq? '1 front) (calc-cov)]
            [(eq? '0 front) 0]
            [(eq? 'e front) 1.0])))))



;Adds coverage info
(define cset
  (lambda (val)
    (set! cov (append cov `(,val)))))


;Evaluates expression and records types found
(define evalRec
  (lambda (exp env)
    (pmatch exp
            (`,num (guard (number? num)) (cset 'e) num)
            (`,bool (guard (boolean? bool)) (cset 'e) bool)
            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
                          (cset '1)
                          (let ((nexp (evalRec e env)))
                            (cond
                              ((not (number? nexp)) (error "expression not number, problem is " l))
                              ((eq? 'inc op) (+ 1 nexp))
                              ((eq? 'dec op) (- nexp 1))
                              ((eq? 'zero? op) (zero? nexp)))))
            (`(if ,t ,c ,a ,l) (cset '2) (cset '1) (let ((texp (evalRec t env)))                                      
                                                     (if  (boolean? texp)
                                                          (if texp
                                                              (begin (cset '1)(evalRec c env))
                                                              (begin (cset '1)(evalRec a env)))
                                                          (error "test not boolean, problem is: " l))))
            (`(lambda (,x : ,T) ,e)
             (cset 'e)
             (set! type-obs (extend-Trec x T type-obs))
             `(closure ,x ,e ,env));)
            
            (`(lambda (,x) ,e)
             (cset 'e)
             `(closure ,x ,e ,env))
            (`(,e1 ,e2 ,l)             
             (cset '3)(cset '1)
             (let ([v1 (evalRec e1 env)]) (cset '1) (let ([v2 (evalRec e2 env)])
                                                      (pmatch v1                                    
                                                              (`(closure ,x ,e11 ,env11)
                                                               (pmatch e2
                                                                       (`(,e3 : ,T3 ,l3) (let ((type2 (resolve-type (type v2)))) 
                                                                                           (if (consistent? type2 T3) 
                                                                                               (set! type-obs (extend-Trec x (meet type2 T3) type-obs))
                                                                                               (error "Bad cast," e3  'is  type2  'not  T3 'blame l3)))) 
                                                                       (`,other (set! type-obs (extend-Trec x (type v2) type-obs))))
                                                               (cset '1)
                                                               (evalRec e11 (extend-env x v2 env11)))
                                                              (`,other (error "what are you even doing here (bad application): " l))
                                                              ;                                                              (`(cast ,l (closure ,x ,id ,e11 ,env11) ,T)
                                                              ;                                                               (set! type-obs (extend-Trec id (type v2) type-obs))
                                                              ;                                                               (cset '1)
                                                              ;                                                               (evalRec e11 (extend-env x id v2 env11)))
                                                              ))))    
            (`(,e : ,T ,l)
             (cset '1)
             (evalRec e env))
            ;`(cast ,l ,(evalRec e env) ,T))
            ;            (`(cast ,l ,e ,T)  ;WHAT DO I DO WITH CASTS???             
            ;             (set! type-obs (extend-Trec (gensym) T type-obs))
            ;             l;(cset '1)
            ;             (cset 'e)
            ;             (evalRec e env))           
            (`,x (guard (symbol? x)) (cset 'e) (let ((ans (env-lookup x env))) ans))
            (`,else (error "Invalid input"))))) 
























;Determines the type of a data value or operation
(define type
  (lambda (exp)
    (pmatch exp
            (`,num (guard (number? num)) `int)
            (`,bool (guard (boolean? bool)) `bool)
            (`(inc ,x ,L) `int)
            (`(dec ,x ,L) `int)
            (`(zero? ,x ,L) `bool)
            (`(closure ,x  ,e ,env) `(-> (type ,x) (type ,e)))
            (`(cast ,l ,e ,T) `,T)))) 

;Inserts types from type-obs into expression
(define insert-types
  (lambda (exp)     
    (pmatch exp           
            (`,num (guard (number? num)) num)
            (`,bool (guard (boolean? bool)) bool)
            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
                          `(,op ,(insert-types e) ,l))
            (`(if ,t ,c ,a ,l) 
             `(if ,(insert-types t) ,(insert-types c) ,(insert-types a) ,l))
            (`(lambda (,x : ,T) ,e)     
             `(lambda (,x : ,(env-lookupT x type-obs)) ,e))    
            (`(lambda (,x) ,e)
             (let ((newtype (env-lookupT x type-obs)))
               (if (equal? newtype 'null)
                   `(lambda (,x) ,(insert-types e))
                   `(lambda (,x : ,newtype) ,(insert-types e)))))
            (`(,e1 ,e2 ,l)             
             `(,(insert-types e1) ,(insert-types e2) ,l))             
            (`(,e : ,T ,l)              
             `(,(insert-types e) : ,T ,l))
            (`,x `,x))))


;;Evaluates expression and records types found
;(define evalRec
;  (lambda (exp env)
;    (pmatch exp
;            (`,num (guard (number? num)) num)
;            (`,bool (guard (boolean? bool)) bool)
;            (`(,op ,e ,l) (guard (member op '(inc dec zero?)))
;                          (let ((nexp (evalRec e env)))
;                            (cond
;                              ((not (number? nexp)) (error "expression not number, problem is " l))
;                              ((eq? 'inc op) (+ 1 nexp))
;                              ((eq? 'dec op) (- nexp 1))
;                              ((eq? 'zero? op) (zero? nexp)))))
;            (`(if ,t ,c ,a ,l) (let ((texp (evalRec t env)))
;                                 (if  (boolean? texp)
;                                      (if texp
;                                          (evalRec c env)
;                                          (evalRec a env))
;                                      (error "test not boolean, problem is: " l))))
;            (`(lambda (,x ,id : ,T) ,e)
;             (set! type-obs (extend-Trec id T type-obs))
;             `(closure ,x ,id ,e ,env));)
;            
;            (`(lambda (,x ,id) ,e)
;             `(closure ,x ,id ,e ,env))
;            (`(,e1 ,e2 ,l) (let* ([v1 (evalRec e1 env)] [v2 (evalRec e2 env)])
;                             (pmatch v1                                    
;                                     (`(closure ,x ,id ,e11 ,env11)
;                                      (set! type-obs (extend-Trec id (type v2) type-obs))                                               
;                                      (evalRec e11 (extend-env x id v2 env11))))))    
;            (`(,e : ,T ,l)
;             `(cast ,l ,e ,T))
;            (`(cast ,l ,e ,T)  ;WHAT DO I DO WITH CASTS???
;             (set! type-obs (extend-Trec (gensym) T type-obs))
;             (evalRec e env))           
;            (`,x (guard (symbol? x)) (let ((ans (env-lookup x env))) ans))
;            (`,else (error "Invalid input"))))))) 

;Extends regular environment
(define extend-env
  (lambda (x y env)
    `(,(cons x y) . ,env)))    



(define extend-Trec
  (lambda (x T env)  
    (let ((vals (hash-ref env x '())))
      (if (member T vals) env
          (hash-set env x (cons T vals))))))

;;Extends type environment
;(define extend-Trec
;  (lambda (x T env)
;    (display "adding ")
;    (display x)
;    (display " ")
;    (display T)
;    (display "\n")
;    (if (null? env) `(,(cons x (list (list T))))
;        (if (equal? x (car (car env)))         
;            `,(cons 
;               (cons x
;                     (cond
;                       [(null? (cdr (car env)))`( ,(cons T (cdr (car env))))]
;                       [(member T (car (cdr (car env)))) `,(cdr (car env))]
;                       [else (list (append (list T) (cdr (car env))))]))              
;               (cdr env))
;            `,(cons (car env) (extend-Trec x T (cdr env)))))))

;Looks up what variables correspond to in environment
(define env-lookup
  (lambda (x env)
    (let ((info (assoc x env)))
      (if info (cdr info) (error "unbound variable" x)))))

;Looks up what ids correspond to in type 
(define env-lookupT
  (lambda (id env)
    ;(let ((info (assoc id env)))
    (let ((info (hash-ref env id '())))
    ;(if info
        (cond
          [(null? info) 'null]
          [(null? (cdr info)) (resolve-type (car info))]
          [else (check-consistency (cdr info) (resolve-type (car info)))]))))
          ;(check-consistency (car (cdr info)) (resolve-type (car (car (cdr info)))))
          ;'null))))

;Checks to see if all types in type env for a given id agree-- they are all the same or some are dyn
(define check-consistency
  (lambda (types type1)
    (if (null? types) type1
        (let ((type2 (resolve-type (car types))))
          (cond    
            [(equal? type1 'dyn) (check-consistency (cdr types) type2)]
            [(equal? type2 'dyn) (check-consistency (cdr types) type1)]
            [(equal? type1 type2) (check-consistency (cdr types) type1)]
            [(consistent? type1 type2) (check-consistency (cdr types) (meet type1 type2))]
            [else (error "types inconsistent" type1"   " (car types))])))))

;returns the type of something, incase it couldn't be done before
(define resolve-type
  (lambda (tv)
    (pmatch tv
            (`int `int)
            (`bool `bool)
            (`dyn `dyn)
            (`(-> ,t1 ,t2) `(-> ,(resolve-type t1) ,(resolve-type t2)))
            (`(type (,op ,e ,L)) (guard (member op '(inc dec))) `int) ;WHAT TO DO WITH E??
            (`(type (zero? ,e ,L)) `bool)
            (`(type ,id) (let ((typed (env-lookupT id type-obs))) (if (equal? `null typed) `dyn typed))))))




;--------------------OTHER FUNCTIONS THAT I NO LONGER USE BUT DON'T WANT TO THROW AWAY--------------------------


(define env-lookup-id               ;possibly unstable...shouldn't have to use, don't currently
  (lambda (x env)
    (let ((info (assoc x env))) 
      (if info (car (cdr info)) (error "id- unbound variable" x)))))

;old coverage functions
(define coverage
  '(0 0))
(define addcov
  (lambda ()    
    (set! coverage (cons (+ 1 (car coverage)) (cdr coverage))))) 
(define subcov
  (lambda ()
    (set! coverage (cons (car coverage) (+ 1 (cadr coverage))))))

;OLD COVERAGE PRINTING
;    (if (equal? '(0) (cdr coverage))  
;        (display "\nCoverage: All expressions evaluated. ") 
;        (begin
;          (display "\nCoverage: At least ")
;          (display  (cdr coverage))
;          (display " of at least ")
;          (display (car coverage))
;          (display " expressions were not evaluated. ")))



(define funapp
  (lambda (fun app)
    (evals (list fun (unique app) (gensym 'BLAME)))))
(define appli
  (lambda (fun app)
    (list fun (unique app) (gensym 'BLAME))))
;--------------------TESTS--------------------------------------------------------------------------------------


(define f1 (unique '(lambda (c : dyn) (if c (lambda (v) (dec v L)) (lambda (w) (inc w L)) L))))
(funapp f1 #t)
(funapp f1 #f)
(define f2 (unique '(((lambda (f) (dec f L)) 9 B) : int M)))
(evals f2)
(define f3 (unique '(lambda (z) (zero? z L))))
(funapp f3 '(7 : int M))
(define f4fail (unique '(lambda (z) (zero? z L))))
(check-error (funapp f4fail '(7 : bool M)))
(define f5 (unique '(lambda (c) (if c (lambda (v) (dec v L)) (lambda (w) (inc w L)) L)))) 
(funapp f5 #t)
       
;(define f6 '(((lambda (c) (if c (lambda (v) (dec v L)) (lambda (w) (inc w L)) L)) 
;          #t 
;          L)
;         7 
;         L))
;(evals '(((lambda (c) (if c (lambda (v) (dec v L)) (lambda (w) (inc w L)) L)) 
;          ((lambda (d) (zero? d L)) 
;           9 
;           L) 
;          L) 7 L))
(define f6 (unique '(lambda (b) (b 7 L))))
(define f7 (unique '(lambda (c) (if c (lambda (v) (dec v L)) (lambda (w) (inc w L)) L ))))
(define f8 (unique '(lambda (d) (zero? d L))))
(funapp f6 (appli f7 (appli f8 9)))
         




(check-error (evals (unique '(if #t #f 7 L))))

  
  
  
  
(check-error (evals (unique '((inc 8 L) 9 M))))

(define f9 (unique '(lambda (x) ((lambda (y) (y x L)) ((lambda (z) (inc (inc z L) L)) : (-> int int) L) L))))
(funapp f9 4)

(define f10 (unique '(lambda (x) x))) 
(funapp f10 (unique '(if #t 6 7 L)))
(define f11 (unique '(lambda (b) (if b 7 8 L))))
(evals (unique `(if #t ,(appli f11 #t) 9 L)))
(evals (unique '(lambda (m) (m 3 L))))

(define f15 (unique '(lambda (j) (j 3 L))))
;(funapp f15 '(lambda (q) (inc q L)))
;(funapp f15 '(lambda (q) (dec q L)))
(define f12 (unique '(lambda (g) ((lambda (h) ((lambda (i) (if i g h L)) #t L)) 4 L))))
(funapp f12 9)
(evals (unique '((lambda (j) (j 3 L)) (lambda (q) (inc q L)) L)))
(evals (unique '((lambda (j) (j 3 L)) (lambda (q) (dec q L)) L)))

  
  
  
  
  
  
;(evals '((lambda (x) (if x 7 #f L)) #f L))
;(evals '((lambda (y) (if #t y 7 L)) #t L))
;(evals '((lambda (y) (if #t y 7 L)) 9 L))
(set! type-obs '())