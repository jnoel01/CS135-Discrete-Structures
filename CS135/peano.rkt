#lang eopl

;;-------------------------------------------------------------------------------
;; Name: Jessica Noel
;; Pledge: I pledge my honor that I have abided by the Stevens Honor System.
;;-------------------------------------------------------------------------------

;; In this lab, we'll implement Peano arithmetic in Scheme.
;; The Peano axioms use induction to formalize
;;   arithmetic with the natural numbers.
;;
;; Peano arithmetic defines the natural numbers inductively.
;;   Zero is the initial natural number,
;;   One is the successor of zero,
;;   Two is the successor of the successor of zero,
;;   Three is the successor of the successor of the successor of zero,
;;   ... and so on for infinitely many numbers.
;;
;; To represent the natural numbers as these successive "peano numbers",
;;   we need a way to programmatically symbolize this inductive (recursive!) process.
;; So we'll use nested lists!
;; We begin by defining zero, our "base case", as the empty list:

(define z '())

;; Then we inductively define the peano numbers:
;;   Given a peano number k, the next peano number (k's successor)
;;   is one level of nesting deeper than k.
;; Here are the first few peano numbers using our representation:
;;   0 = '()
;;   1 = '(())
;;   2 = '((()))
;;   3 = '(((())))
;;   and so on forever...
;;
;; Is this representation cumbersome? Yes, for sure.
;; But we're going to write our functions in such a way
;;   that this internal nested list representation of the natural numbers
;;   is abstracted away from the arithmetic we implement.




;;-------------------------------------------------------------------------------
;;                               HELPER FUNCTIONS
;;-------------------------------------------------------------------------------

;; Below are four helper functions given to you to aid in testing your code.
;; You may NOT use any of these functions in the functions you implement!
;; They are strictly for making testing easier.


;; "itp" converts a decimal integer to
;;   its corresponding peano representation.
;; The function raises an exception upon receiving a negative number.
;;
;; Examples:
;; (itp 0) -> '()
;; (itp 2) -> '((()))
;; (itp 5) -> '(((((())))))
;; (itp -1) -> <conversion error>
;;
;; Type signature: (itp int) -> peano
(define (itp i)
  (cond
    [(zero? i) z]
    [(positive? i)
     (list (itp (- i 1)))]
    [else (eopl:error "Error converting to peano: argument cannot be negative!")]))

;; "pti" converts from a nested list peano number
;;   to its corresponding decimal number.
;;
;; Examples:
;; (pti '() ) -> 0
;; (pti '((())) ) -> 2
;; (pti '(((((()))))) ) -> 5
;;
;; Type signature: (pti peano) -> int
(define (pti p)
  (if (null? p) 0
      (+ 1 (pti (car p)))))


;; Here are two functions to expedite running test cases.
;; They do the work for you of converting in and out of
;;   our nested list representation of the natural numbers.

;; "tst1" receives a one-input peano function and an integer,
;;   converts the integer to peano form, and runs the function on it.
;;
;; Type signature: (tst1 p-function int) -> int/bool
(define (tst1 func a)
  (let ([res (func (itp a))])
    (if (list? res) (pti res) res)))

;; "tst2" receives a two-input peano function and two integers,
;;   converts the integers to peano form, and runs the function on them.
;;
;; Type signature: (tst2 p-function int int) -> int/bool
(define (tst2 func a b)
  (let ([res (func (itp a) (itp b))])
    (if (list? res) (pti res) res)))




;;-------------------------------------------------------------------------------
;;                          ATOMIC PEANO OPERATIONS
;;-------------------------------------------------------------------------------

;; Here, we'll write three fundamental operations on peano numbers.
;; From these basic operations, we'll build more complex operations.


;; Implement "pz?", which accepts a peano number p
;;   and returns whether p is zero.
;; Recall that in our implementation,
;;   we represent zero with the empty list.
;; (Or just use 'equal?' to compare it to the variable 'z')
;;
;; Examples:
;; (tst1 pz? 0) -> #t
;; (tst1 pz? 1) -> #f
;; (tst1 pz? 40) -> #f
;;
;; Type signature: (pz? peano) -> bool
(define (pz? p)
  (equal? p z))    ;z is 0, so just checks if p=0



;; Implement "succ", which accepts a peano number p
;;   and returns the successor of p.
;; Recall that in our implementation,
;;   a peano number's successor is one level of nesting deeper.
;;
;; Examples:
;; (succ '(()) ) -> '((()))
;; (succ '(((()))) ) -> '((((()))))
;; (tst1 succ 0) -> 1
;; (tst1 succ 5) -> 6
;; (tst1 succ 21) -> 22
;; (pti (succ (succ (itp 3)))) -> 5
;;
;; Type signature: (succ peano) -> peano
(define (succ p)
  (list p))   ;when doing list you add another set of parenthesis which in peano shows the sucessor



;; Implement "pred", which accepts a peano number p
;;   and returns the predecessor of p.
;; Recall that in our implementation,
;;   each integer is a nested list one level shallower
;;   than the next integer.
;;
;; One of Peano's axioms states that zero has no predecessor.
;; So if the input to pred is zero, we need to fail somehow.
;; We'll do this by raising an exception.
;; Put the following line in your code and have it execute
;;   when the input value is zero:
;;   (eopl:error "pred error: zero has no predecessor!")
;;
;; Examples:
;; (pred '((())) ) -> '(())
;; (pred '() ) -> <pred error>
;; (tst1 pred 1) -> 0
;; (tst1 pred 38) -> 37
;; (pti (pred (pred (pred (itp 14))))) -> 11
;;
;; Type signature: (pred peano) -> peano
(define (pred p)
 (if (equal? p z)    ;checks if p equal to z, if it is, throw error
     (eopl:error "pred error: zero has no predecessor!")
  (car p)))  ;else first element in p
  


;;-------------------------------------------------------------------------------
;;                          COMPLEX PEANO OPERATIONS
;;-------------------------------------------------------------------------------

;; Now that we have the basic operations of
;;   succession, predecession, and comparsion with zero,
;;   we can implement other familiar arithmetic operations.
;; From this point forward, the fact that we are using nested lists
;;   to represent numbers becomes completely irrelevant.
;; The internal use of lists is abstracted away by using
;;   the variable 'z', and the functions 'succ', 'pred', and 'pz?'.
;; Pretend you don't know that we're using nested lists:
;;   DO NOT use list-related functions like cdr, car, list, null?, and so on.
;;   DO NOT use any list literals like '((())).
;;     For '(), use z; for '((())), use (succ (succ z)); etc.


;; First, we'll write the addition operator.
;; Implement "p+" to accept two peano numbers
;;   and return their sum as a peano number.
;; Again, DO NOT convert in and out of the peano form
;;   to do the addition! Use the atomic operations you wrote.
;;
;; Examples:
;; (p+ '((())) '(()) ) -> '(((())))
;; (tst2 p+ 0 0) -> 0
;; (tst2 p+ 5 4) -> 9
;; (tst2 p+ 1 6) -> 7
;; (tst2 p+ 0 10) -> 10
;;
;; Type signature: (p+ peano peano) -> peano
(define (p+ a b)   
  (if (pz? a)     ;if a=0 return b
      b
  (if (pz? b)     ;if b=0 return a
      a
      (p+ (succ a)(pred b)))))   ;take the sucessor and the pred then add them together to to addition on both a b
      


;; Next, implement "p-" to accept two peano numbers a and b
;;   and return their difference, a - b, as a peano number.
;; This operation has a catch: since there are no negative peano numbers,
;;   we can't compute a - b if a < b.
;; If this problem occurs, raise an exception
;;   by executing the following line:
;;   (eopl:error "subtraction error: a < b!")
;; Since we haven't implemented the '<' operator,
;;   figure out how else we'll know
;;   when this problem will occur.
;;
;; Examples:
;; (p- '((((())))) '((())) ) -> '((()))
;; (tst2 p- 12 12) -> 0
;; (tst2 p- 6 4) -> 2
;; (tst2 p- 4 6) -> <subtraction error>
;; (tst2 p- 30 19) -> 11
;; (tst2 p- 10 0) -> 10
;;
;; Type signature: (p- peano peano) -> peano
(define (p- a b)
 (if(and (pz? a)(not(pz? b)))   ;a=0 AND b not 0 itll be negative so throw error
      (eopl:error "subtraction error: a < b!")
  (if(pz? a)     ;a=0 return b
     b                           ;any number minus 0 is just itself
   (if(pz? b)     ;b=0 return a
      a
      (p-(pred a)(pred b))))))  ;take pred of a and preb of b
      
 

;; Implement "p*" to accept two peano numbers
;;   and return their product.
;; If you're not sure how to go about this,
;;   think back to how you first learned
;;   the concept of multiplication of whole numbers
;;   in elementary school -
;;   multiplication is just repeated _________.
;; Taking advantage of functions you've already written
;;   will make writing this one much easier.
;;
;; Examples:
;; (p* '(((()))) '((())) ) -> '((((((()))))))
;; (tst2 p* 0 0) -> 0
;; (tst2 p* 3 0) -> 0
;; (tst2 p* 4 3) -> 12
;; (tst2 p* 1 7) -> 7
;; (tst2 p* 17 5) -> 85
;;
;; Type signature: (p* peano peano) -> peano
(define (p* a b)    
  (if (or(pz? a) (pz? b))       ;if a=0 or b=0 return 0 (anything times 0 is 0)
     z
      (p+ a(p* a(pred b)))))    ;if neither a or b are 0
 


;; Implement "p^" to accept peano numbers a and b
;;   and return a^b (a raised to the power of b) as a peano number.
;; Like p*, think about how exponentiation is explained
;;   in elementary school: it's just repeated _________.
;;
;; Be careful when testing this function.
;; The numbers can get big really quickly,
;;   and our implementation with nested lists and recursion
;;   won't take too kindly to large computations.
;;
;; You may have 0^0 evaluate to 1 (we aren't going to test it).
;;
;; Examples:
;; (p^ '((())) '(((()))) ) -> '((((((((()))))))))
;; (tst2 p^ 0 4) -> 0
;; (tst2 p^ 5 0) -> 1
;; (tst2 p^ 4 2) -> 16
;; (tst2 p^ 3 3) -> 27
;; (tst2 p^ 2 7) -> 128
;;
;; Type signature: (p^ peano peano) -> peano
(define (p^ a b)
 (if(pz? a)    ;if a=0 return 0
     z
  (if(pz? b)    ;if b=0 return succ of 0 (1), bc anything to 0 is 1
     (succ z)
      (p* a(p^ a(pred b))))))   ;else use multiplication func to do exp




;; Implement "p=" to accept two peano numbers
;;   and return whether they are equal.
;; Pretend we don't have a built-in Scheme function
;;   to compare the two inputs.
;; The only function we have to work with
;;   for comparing peano numbers is "pz?".
;;
;; Examples:
;; (p= '((())) '(()) ) -> #f
;; (p= '(((()))) '(((()))) ) -> #t
;; (tst2 p= 3 16) -> #f
;; (tst2 p= 5 5) -> #t
;; (tst2 p= 0 0) -> #t
;;
;; Type signature: (p= peano peano) -> bool
(define (p= a b)
  (if (and (pz? a) (pz? b))  ;if a and b are equal to 0
      #t
  (if (or (pz? a) (pz? b))   ;if one (a,b) are 0 they're not equal #f
      #f
      (p=(pred a)(pred b))))) ;check is predessor of a and b are equal




;; Implement "p>" to accept peano numbers a and b
;;   and return whether a > b.
;; Again, this isn't trivial because you can't simply
;;    convert the inputs to regular integers and
;;    compare them with the built-in > operator.
;; And you can't simply subtract because it'll raise an error!
;;
;; Examples:
;; (p> '((())) '(()) ) -> #t
;; (tst2 p> 4 6) -> #f
;; (tst2 p> 3 3) -> #f
;; (tst2 p> 7 2) -> #t
;;
;; Type signature: (p> peano peano) -> bool
(define (p> a b)
  (if (or(pz? a) (p= a b))   ;if a=0 or a and b are the same number a cant be greater than b
      #f
   (if (pz? b)     ;if b=0 a will always be greater
       #t
       (p> (pred a) (pred b)))))   ;take preb of a and pred of b and apply p>



;; Implement "p>=" to accept peano numbers a and b
;;   and return whether a >= b.
;; This one should be really easy now!
;;
;; Examples:
;; (p>= '((())) '(()) ) -> #t
;; (tst2 p>= 4 6) -> #f
;; (tst2 p>= 3 3) -> #t
;; (tst2 p>= 7 2) -> #t
;;
;; Type signature: (p>= peano peano) -> bool
(define (p>= a b)
  (if (or(p= a b)(pz? b))  ;if a=b or b is 0 return true bc theyre either = or a is greater bc b is 0
      #t
      (p> (pred a) (pred b)))) ;use same else as greater than func above
       
    

;; Implement "p%" to accept peano numbers a and b
;;   and return a mod b (a % b),
;;   the remainder of dividing a by b.
;; Remember: integer division is repeated ________.
;; The modulo operator is undefined when
;;   the divisor is zero, so once again we'll introduce an error.
;; Execute the following code to raise an exception if b is zero:
;;   (eopl:error "modulo error: mod is zero!")
;;
;; Examples:
;;   (p% '(((((()))))) '(((()))) ) -> '((()))
;;   (tst2 p% 6 0) -> <modulo error>
;;   (tst2 p% 3 5) -> 3
;;   (tst2 p% 0 6) -> 0
;;   (tst2 p% 30 15) -> 0
;;   (tst2 p% 8 1) -> 0
;;   (tst2 p% 124 17) -> 5
;;   (tst2 p% 76 9) -> 4
;;
;; Type signature: (p% peano peano) -> peano
(define (p% a b)  
  (if (pz? b)       ;if b is equal to 0 its undefined
      (eopl:error "modulo error: mod is zero!")
  (if (pz? a)      ;if a is equal to 0 just return 0
      z
   (if(p> b a)     ;if b is > a return a 
      a
      (p% (p- a b)  ;modulus of a-b return b
      b)))))




;; Implement "p-even?" to accept a peano number p
;;   and return whether p is even.
;;
;; Examples:
;;   (p-even? '((((())))) ) -> #t
;;   (tst1 p-even? 0) -> #t
;;   (tst1 p-even? 1) -> #f
;;   (tst1 p-even? 25) -> #f
;;   (tst1 p-even? 76) -> #t
;;
;; Type signature: (p-even? peano) -> bool
(define (p-even? p)
  (pz?(p% p (succ(succ z)))))  ;see if the modulus is z when mod by 2


;; Implement "p-prime?" to accept a peano number p
;;   and return whether p is a prime number.
;; Zero and one are not prime.
;; You'll likely need to write a helper function for this one!
;;
;; Examples:
;;   (p-prime? '(((((((()))))))) ) -> #t
;;   (tst1 p-prime? 0) -> #f
;;   (tst1 p-prime? 2) -> #t
;;   (tst1 p-prime? 5) -> #t
;;   (tst1 p-prime? 9) -> #f
;;   (tst1 p-prime? 35) -> #f
;;   (tst1 p-prime? 37) -> #t
;;
;; Type signature: (p-prime? peano) -> bool
(define (p-prime? p)
  (if (or(pz? p) (pz? (pred p)))   ;if p is 0 or the pred of p is 0 then
      #f                              ;it must be false, bc impossible to be prime
  (if (p> p (succ z))        ;if p greater than succ of p use helper
          (h-prime? p (succ(succ z)))
      #f)))


 ;;HELPER FUNCTION
      (define (h-prime? a b)
        (if (p= a b)   ;if a and b are equal it must be true
            #t
            (if(pz? (p% a b))  ;take mod of a and b and see if its 0, if so it has
               #f                ;to be false bc its divisible by #
               (h-prime? a(succ b))))) ;else take succ of b and see if a b are prime




;; Created March 2020 by Jared Pincus