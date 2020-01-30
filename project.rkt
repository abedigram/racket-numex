;; PL Project - Fall 2018
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool (b) #:transparent) ;; a boolean var e.g., (bool #t)

(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct minus  (e1 e2)  #:transparent)  ;; subtracts two expressions

(struct mult  (e1 e2)  #:transparent)  ;; multiplies two expressions
(struct div  (e1 e2)  #:transparent)  ;; divides two expressions

(struct neg  (e1)  #:transparent)  ;; negates two expressions
(struct andalso  (e1 e2)  #:transparent)  ;; and result of two expressions
(struct orelse  (e1 e2)  #:transparent)  ;; or result of two expressions

(struct iseq  (e1 e2)  #:transparent)  ;; comparison two expressions

(struct cnd  (e1 e2 e3)  #:transparent)  ;; if e1 is true evaluate e2 else e3 two expressions
(struct ifnzero  (e1 e2 e3)  #:transparent)  ;; if e1 is not zero evaluate e2 else e3 two expressions
(struct ifleq  (e1 e2 e3 e4)  #:transparent)  ;; e1 <= e2 ? e3 : e4

(struct with  (s e2 e3)  #:transparent)  ;; let e1 be s in e2
(struct apair (e1 e2) #:transparent) ;; list constructor
(struct 1st (e1) #:transparent) ;; car of pair
(struct 2nd (e1) #:transparent) ;; cdr of pair


(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application


(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 


(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
;(struct record (k m) #:transparent) ;; record holds munit
(struct record (k r) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r

(struct letrec (s1 e1 s2 e2 e3) #:transparent) ;; a letrec expression for recursive definitions

;; Problem 1

(define (racketlist->numexlist xs) (cond [ (null? xs)(munit)]  [true (apair (car xs)(racketlist->numexlist (cdr xs)) )] ))          ;;done
(define (numexlist->racketlist xs) (cond [ (munit? xs) '()]  [true (cons (apair-e1 xs)(numexlist->racketlist (apair-e2 xs)) )] ))   ;;done

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
  		  [(eq? (car (car env)) str) (cdr (car env))]
        [true (envlookup (cdr env) str) ]
		)
 )

(define (createNewEnv env actuals)
  (cond [(null? env) actuals]
        [true (cons (car env) (createNewEnv (cdr env) actuals))]))

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]

        [(num? e) ; Integer value
         (cond
           [(integer? (num-int e)) e]
           [true (error (format "NUMEX:) num must be integer"))])]

        [(bool? e) ; Integer value
         (cond
           [(boolean? (bool-b e)) e]
           [true (error (format "NUMEX:) bool must be boolean"))])]
        
        [(munit? e) (munit)]
        [(closure? e) e]
                      
        [(plus? e) ;;plus 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX:) addition applied to non-number")))]
        
        [(minus? e) ;;minus
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX:) sunbtraction applied to non-number")))]

        [(mult? e) ;;mult
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX:) multiply applied to non-number")))]
        
        [(div? e) ;;division
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (quotient (num-int v1) 
                       (num-int v2)))
               (error "NUMEX:) division applied to non-number")))]

        [(neg? e) ;;negation
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (cond [(num? v1) (num (- (num-int v1) ))]
                 [(bool? v1) (bool (not (bool-b v1) ))]
               [#t (error "NUMEX:) neg applied to non-number")]))]

        [(andalso? e) ;;and
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (cond 
                [(and (bool? v1)
                    (not (bool-b v1)))
               (bool (bool-b v1) )]           
              [(and (bool? v1)
                    (bool? (eval-under-env (andalso-e2 e) env)))
               (bool (and (bool-b v1) 
                       (bool-b (eval-under-env (andalso-e2 e) env))))]

               (error "NUMEX:) andalso applied to non-boolean")))]

        [(orelse? e) ;;or
         (let ([v1 (eval-under-env (orelse-e1 e) env)]
               [v2 (eval-under-env (orelse-e2 e) env)])
           (cond [(and (bool? v1)
                    (bool? v2))
               (bool (or (bool-b v1) 
                       (bool-b v2)))]
                [(and (bool? v1)
                    (bool-b v1))
               (bool (bool-b v1) )]
               (error "NUMEX:) orelese applied to non-boolean")))]

        [(iseq? e) ;;iseq
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (cond 
           [(and (num? v1)(num? v2))(bool (eq? (num-int v1)(num-int v2)))]
           [(and (bool? v1)(bool? v2))(bool (eq? (bool-b v1)(bool-b v2)))]
           [(and (bool? v1)(num? v2))(bool #f)]
           [(and (num? v1)(bool? v2))(bool #f)]
               (error "NUMEX:) equlality applied to not boolean/num")))]

        [(ismunit? e) ;;ismunit
         (let ([v1 (eval-under-env (ismunit-e e) env)])
           (cond 
           [(munit? v1)(bool #t)]
           [#t (bool #f)]
               (error "NUMEX:) not applicable to ismunit")))]

        [(apair? e) ;apair maker
         (let([v1 (eval-under-env (apair-e1 e) env)]
              [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))]

         [(cnd? e)
          (let ([v1 (eval-under-env (cnd-e1 e) env)])
             (if (bool? v1)
                 (if (bool-b  v1)
                     (eval-under-env (cnd-e2 e) env)
                     (eval-under-env (cnd-e3 e) env))
                 (error "NUME:) not applicable operands to cnd")))]     

         [(ifnzero? e)
          (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
             (if (num? v1)
                 (if (not (eq? (num-int v1) 0))
                     (eval-under-env (ifnzero-e2 e) env)
                     (eval-under-env (ifnzero-e3 e) env))
                 (error "NUMEX:) not applicable operands to cnd")))]

         [(ifleq? e)
          (let ([v1 (eval-under-env (ifleq-e1 e) env)]
               [v2 (eval-under-env (ifleq-e2 e) env)])
             (if (and (num? v1)(num? v2))
                 (if (or (> (num-int v2) (num-int v1)) (eq? (num-int v2) (num-int v1) ))
                     (eval-under-env (ifleq-e3 e) env)
                     (eval-under-env (ifleq-e4 e) env))
                 (error "NUMEX:) not applicable operands to ifleq" e)))]  

        [(1st? e) ;;division
         (let ([v1 (eval-under-env (1st-e1 e) env)])
           (if  (apair? v1)
               (apair-e1 v1)
               (error "NUMEX:) not apair")))]                               

        [(2nd? e) ;;division
         (let ([v1 (eval-under-env (2nd-e1 e) env)])
           (if  (apair? v1)
               (apair-e2 v1)
               (error "NUMEX:) not apair")))]                               


        [(apply? e)
          (let (  [fClosure (eval-under-env (apply-funexp e) env)])
            (if (or (closure? fClosure) (lam? fClosure))
              (if (lam? fClosure)
                (let* ([flam (eval-under-env fClosure env)] 
                      [func (closure-f flam)])
                  (if (lam? func)
                    (let ([evaled (eval-under-env (apply-actual e) env)])
                      (eval-under-env (lam-body func) (cons (cons (lam-formal func) evaled)
                                                      (cons (cons (lam-nameopt func) flam) (closure-env flam)))))
                    (error "Application must be performed on a function")))
                (let ([func (closure-f fClosure)])
                  (if (lam? func)
                    (let ([evaled (eval-under-env (apply-actual e) env)])
                      (eval-under-env (lam-body func) (cons (cons (lam-formal func) evaled)
                                                      (cons (cons (lam-nameopt func) fClosure) (closure-env fClosure)))))
                    (error "Application must be performed on a function"))))
              (error (format "First argument must be a closure: ~V" fClosure))))]

         [(lam? e)
         (if (and (or (string? (lam-nameopt e)) (null? (lam-nameopt e))) (string? (lam-formal e)))
             (closure env e)
             (error "NUMEX:) function name and parameter name must be string"))]                          

         [(with? e)
          (let ([v1 (eval-under-env (with-e2 e) env)]
                [s (with-s e)])
             (if (string? s)
                 (eval-under-env (with-e3 e) (append env (list (cons s v1))))
                 (error "NUMEX:) with expected string")))]

         [(letrec? e) 
          (eval-under-env (letrec-e3 e) (cons (cons (letrec-s1 e) (letrec-e1 e)) (cons (cons (letrec-s2 e) (letrec-e2 e) ) env)) )

         ]
        ;; CHANGE add more cases here
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3) (cnd (ismunit e1) e2 e3))
 
 (define (with* bs e2) "CHANGE")
 
 (define (ifneq e1 e2 e3 e4) (cnd (iseq e1 e2) e4 e3))

;; Problem 4

 (define numex-filter "CHANGE")
 
 (define numex-all-gt "CHANGE")

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))

(define f (
  lam "f" "x"
      (ifneq (var "x") (num 0)
        (ifneq (var "x") (num 1)
          (plus (apply (var "f") (minus (var "x") (num 1))) (apply (var "f") (minus (var "x") (num 2))))
          (num 1)
        )
        (num 0))
      
      ;(apply (var "f") (minus (var "x") (num 1)))
)) 

(eval-exp (apply f (num 5)))