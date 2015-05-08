(load "load")

  (define group-axioms
   (list
    (rule '( (?? a) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) 1 (?? b))
	  `( ,@a  ,@b ))
    (rule '( (?? a) (?? c) (- (?? c)) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) (- (?? c)) (?? c) (?? b))
	  `( ,@a ,1 ,@b ))))

;;(pp (try-rules '(a) assumptions 
;;	       (lambda (result fail)
;;	       (pp result)
;;		 )
;;	       (lambda () #f)
;;	       )) 

(define (try-push outcome start results)
	;;(pp "try to push")
	;;(pp results)
	(let* ((story (cons start (cadr (assoc start results))))
	       (n-story (length story))
		(old-vcell (assoc outcome results)))
	       (if old-vcell
		(let* ((old-story (cadr old-vcell))
		       (n-old-story (length old-story)))
		   (if (< n-story n-old-story)
			(cons (list outcome story) results)
			results))
		(cons (list outcome story) results)  )))

(define (deduce vars starters assumptions results)
  (define gen-assumptions
    (append 
     assumptions
  (let per-var ((vars  vars)
		(new-assumptions '())) 
	(if (pair? vars)
	  (per-var  (cdr vars) 
		   (cons (rule '( (?? a) 1 (?? b))
			       `( ,@a ,(car vars) (- ,(car vars)) ,@b ))
		    (cons
		     	(rule '( (?? a) 1 (?? b))
	  		`( ,@a (- ,(car vars)) ,(car vars) ,@b ))
		     new-assumptions)) )
	  new-assumptions
	 )	
    )))
  (let per-start ((starters starters)
		  (assumptions gen-assumptions)
		  (results results))
    	;;(pp "per-start")
	(if (pair? starters)
	  (let per-assumption ((start (car starters))
			(new-starters (cdr starters))
			(assumptions assumptions)
			(current-assumptions assumptions)
			(results results))
	    	;;(pp "per-assumption")
	    	(if (pair? current-assumptions)
		  ((car current-assumptions) start
				     (lambda (outcome f)
				     (per-assumption start new-starters assumptions (cdr current-assumptions ) (try-push outcome start results)))
				     (lambda () 
				      (per-assumption start new-starters assumptions (cdr current-assumptions ) results)))
		  (per-start new-starters assumptions results)))
	  results)))



 (define hypothesis
   (list (rule '((?? x) a b (?? y))
	 `( ,@x a c ,@y ))))
#|
 (define hypothesis
	(list  (rule '( (?? a) (?? b) (? c))
	  `( ,@a r ,@b ,c))
	 (rule '((? c) (?? a) (?? b) )
	  `(,c ,@a r ,@b))

    (rule '( (?? a) r (?? b) (? c))
	  `( ,@a  ,@b ,c))
(rule '((? c) (?? a) r (?? b) )
	  `(,c ,@a  ,@b))

))
|#
(define assumptions
   (append group-axioms hypothesis))

(define theorem
  '((b) (c))
  )


(define (proof variables assumptions  theorem-start theorem-end)
  	
 	(let lp ((starters `(,theorem-start))
		(end theorem-end)
		(assumptions assumptions)
		(variables variables)
		(results `((,theorem-start ()))))
		(let* ((new-results (deduce variables starters assumptions results))
		       (vcell (assoc end results)))
			(if vcell
			  (cons end (cadr  vcell))
			  (lp (map car results) end assumptions variables new-results)
			  )
		))) 

(define (ppp lst)
  	(if (pair? lst)
	  (let ((new-lst (cdr lst)))
	    (ppp new-lst)
	    (pp (car lst))
	     )
	  (pp "Proved:"))
	  )

(pp (proof '(a b c) group-axioms '( (- a b c)) '((- c) (- b) (- a))))

;;(ppp (proof '(a b) group-axioms '(1) '((- b)(- a) a b )))

;;(ppp (proof '(r) assumptio|ns '(r) '(1)))
;;
(pp (proof '(a b c) assumptions '(b) '(c) ))
;;;;           Most General Generic-Operator Dispatch
(declare (usual-integrations))		; for compiler

;;; Generic-operator dispatch is implemented here by a
;;; discrimination list (a "trie", invented by Ed Fredkin),
;;; where the arguments passed to the operator are examined
;;; by predicates that are supplied at the point of
;;; attachment of a handler.  (Handlers are attached by
;;; ASSIGN-OPERATION alias DEFHANDLER).

;;; The discrimination list has the following structure: it
;;; is an improper alist whose "keys" are the predicates
;;; that are applicable to the first argument.  If a
;;; predicate matches the first argument, the cdr of that
;;; alist entry is a discrimination list for handling the
;;; rest of the arguments.  Each discrimination list is
;;; improper: the cdr at the end of the backbone of the
;;; alist is the default handler to apply (all remaining
;;; arguments are implicitly accepted).

;;; A successful match of an argument continues the search
;;; on the next argument.  To be the correct handler all
;;; arguments must be accepted by the branch predicates, so
;;; this makes it necessary to backtrack to find another
;;; branch where the first argument is accepted if the
;;; second argument is rejected.  Here backtracking is
;;; implemented using #f as a failure return, requiring
;;; further search.

#| ;;; For example.
(define foo (make-generic-operator 2 'foo))

(defhandler foo + number? number?)

(define (symbolic? x)
  (or (symbol? x)
      (and (pair? x) (symbolic? (car x)) (list? (cdr x)))))

(define (+:symb x y) (list '+ x y))

(defhandler foo +:symb number? symbolic?)
(defhandler foo +:symb symbolic? number?)
(defhandler foo +:symb symbolic? symbolic?)

(foo 1 2)
;Value: 3

(foo 1 'a)
;Value: (+ 1 a)

(foo 'a 1)
;Value: (+ a 1)

(foo '(+ a 1) '(+ 1 a))
;Value: (+ (+ a 1) (+ 1 a))
|#

(define (make-generic-operator arity
                   #!optional name default-operation)
  (let ((record (make-operator-record arity)))

    (define (operator . arguments)
      (if (not (acceptable-arglist? arguments arity))
          (error:wrong-number-of-arguments
           (if (default-object? name) operator name)
           arity arguments))
      (apply (find-handler (operator-record-tree record)
                           arguments)
             arguments))

    (set-operator-record! operator record)

    (set! default-operation
      (if (default-object? default-operation)
          (named-lambda (no-handler . arguments)
            (error "Generic operator inapplicable:"
                   (if (default-object? name) operator name)
                   arguments))
          default-operation))
    (if (not (default-object? name))    ; Operation by name
        (set-operator-record! name record))

    (assign-operation operator default-operation)
    operator))

#|
;;; To illustrate the structure we populate the
;;; operator table with quoted symbols rather 
;;; than actual procedures.  

(define blend
  (make-generic-operator 2 'blend 'blend-default))

(pp (get-operator-record blend))
(2 . blend-default)

(defhandler blend 'b+b 'blue?  'blue?)
(defhandler blend 'g+b 'green? 'blue?)
(defhandler blend 'b+g 'blue?  'green?)
(defhandler blend 'g+g 'green? 'green?)

(pp (get-operator-record blend))
(2 (green? (green? . g+g) (blue? . g+b))
   (blue? (green? . b+g) (blue? . b+b))
   .
   blend-default)
|#

#|
;;; Backtracking

;;; An operator satisfies bleen? 
;;; if it satisfies either blue? or green?

(defhandler blend 'e+r 'bleen? 'red?)
(defhandler blend 'e+u 'bleen? 'grue?)

(pp (get-operator-record blend))
(2 (bleen? (grue? . e+u) (red? . e+r))
   (green? (green? . g+g) (blue? . g+b))
   (blue? (green? . b+g) (blue? . b+b))
   .
   blend-default)

;;; Consider what happens if we invoke
;;; (blend <bleen> <blue>)
|#

;;; This is the essence of the search.

(define (find-handler tree args)
  (if (null? args)
      tree
      (find-branch tree
		   (car args)
		   (lambda (result)
		     (find-handler result
				   (cdr args))))))

(define (find-branch tree arg next)
  (let loop ((tree tree))
    (cond ((pair? tree)
           (or (and ((caar tree) arg)
                    (next (cdar tree)))
               (loop (cdr tree))))
          ((null? tree) #f)
          (else tree))))

(define (assign-operation operator handler
                          . argument-predicates)
  (let ((record (get-operator-record operator))
        (arity (length argument-predicates)))
    (if record
        (begin
          (if (not (<= arity
                       (procedure-arity-min
                        (operator-record-arity record))))
              (error "Incorrect operator arity:" operator))
          (bind-in-tree argument-predicates
                        handler
                        (operator-record-tree record)
                        (lambda (new)
                          (set-operator-record-tree! record
                                                     new))))
        (error "Undefined generic operator" operator)))
  operator)

(define defhandler assign-operation)

(define (bind-in-tree keys handler tree replace!)
  (let loop ((keys keys) (tree tree) (replace! replace!))
    (cond ((pair? keys)   ; more argument-predicates
	   (let find-key ((tree* tree)) 
	     (if (pair? tree*)
		 (if (eq? (caar tree*) (car keys))
		     ;; There is already some discrimination
		     ;; list keyed by this predicate: adjust it
		     ;; according to the remaining keys
		     (loop (cdr keys)
			   (cdar tree*)
			   (lambda (new)
			     (set-cdr! (car tree*) new)))
		     (find-key (cdr tree*)))
		 (let ((better-tree
			(cons (cons (car keys) '()) tree)))
		   ;; There was no entry for the key I was
		   ;; looking for.  Create it at the head of
		   ;; the alist and try again.
		   (replace! better-tree)
		   (loop keys better-tree replace!)))))
	  ;; cond continues on next page.

	  ((pair? tree)  ; no more argument predicates.
            ;; There is more discrimination list here,
            ;; because my predicate list is a proper prefix
            ;; of the predicate list of some previous
            ;; assign-operation.  Insert the handler at the
            ;; end, causing it to implicitly accept any
            ;; arguments that fail all available tests.
	   (let ((p (last-pair tree)))
	     (if (not (null? (cdr p)))
		 (warn "Replacing a default handler:"
		       (cdr p) handler))
	     (set-cdr! p handler)))
	  (else
	   ;; There is no discrimination list here.  This
	   ;; handler becomes the discrimination list,
	   ;; accepting further arguments if any.
	   (if (not (null? tree))
	       (warn "Replacing a handler:" tree handler))
	   (replace! handler)))))

(define *generic-operator-table* (make-eq-hash-table))

(define (get-operator-record operator)
  (hash-table/get *generic-operator-table* operator #f))

(define (set-operator-record! operator record)
  (hash-table/put! *generic-operator-table* operator
                   record))

(define (make-operator-record arity) (cons arity '()))
(define (operator-record-arity record) (car record))
(define (operator-record-tree record) (cdr record))
(define (set-operator-record-tree! record tree)
  (set-cdr! record tree))

(define (acceptable-arglist? lst arity)
  (let ((len (length lst)))
    (and (fix:<= (procedure-arity-min arity) len)
         (or (not (procedure-arity-max arity))
             (fix:>= (procedure-arity-max arity) len)))))

#|
;;; Demonstration of handler tree structure.
;;; Note: symbols were used instead of procedures

(define foo (make-generic-operator 3 'foo 'foo-default))

(pp (get-operator-record foo))
(3 . foo-default)

(defhandler foo 'two-arg-a-b 'a 'b)
(pp (get-operator-record foo))
(3 (a (b . two-arg-a-b)) . foo-default)

(defhandler foo 'two-arg-a-c 'a 'c)
(pp (get-operator-record foo))
(3 (a (c . two-arg-a-c) (b . two-arg-a-b)) . foo-default)

(defhandler foo 'two-arg-b-c 'b 'c)
(pp (get-operator-record foo))
(3 (b (c . two-arg-b-c))
   (a (c . two-arg-a-c) (b . two-arg-a-b))
   . foo-default)
|#

#|
(defhandler foo 'one-arg-b 'b)
(pp (get-operator-record foo))
(3 (b (c . two-arg-b-c) . one-arg-b)
   (a (c . two-arg-a-c) (b . two-arg-a-b))
   . foo-default)

(defhandler foo 'one-arg-a 'a)
(pp (get-operator-record foo))
(3 (b (c . two-arg-b-c) . one-arg-b)
   (a (c . two-arg-a-c) (b . two-arg-a-b) . one-arg-a)
   .
   foo-default)

(defhandler foo 'one-arg-a-prime 'a)
;Warning: Replacing a default handler: 
;         one-arg-a one-arg-a-prime

(defhandler foo 'two-arg-a-b-prime 'a 'b)
;Warning: Replacing a handler: 
;         two-arg-a-b two-arg-a-b-prime

(defhandler foo 'three-arg-x-y-z 'x 'y 'z)
(pp (get-operator-record foo))
(3 (x (y (z . three-arg-x-y-z)))
   (b (c . two-arg-b-c) . one-arg-b)
   (a (c . two-arg-a-c)
      (b . two-arg-a-b-prime)
      . 
      one-arg-a-prime)
   .
   foo-default)
|#

;;; Compatibility with previous extensible generics

(define make-generic-operation make-generic-operator)

(define (add-to-generic-operation! operator
				   applicability
				   handler)
  ;; An applicability is a list representing a
  ;; disjunction of lists, each representing a
  ;; conjunction of predicates.

  (for-each (lambda (conj)
	      (apply assign-operation
		     operator
		     handler
		     conj))
	    applicability))

				;;;; File:  load.scm -- Loader for pattern matching system

; Pattern matcher:

(load "ghelper")
(load "matcher")


; Term rewriting / pattern-directed invocation system:

(define (rule-memoize f) f) ; A stub put in place in case you want to
                            ; play with memoization in the term
                            ; rewriter

(load "utils")
(load "rule-implementation")
(load "rules")

(load "pattern-operator")
;;;; Matcher based on match combinators, CPH/GJS style.
;;;     Idea is in Hewitt's PhD thesis (1969).

(declare (usual-integrations))

;;; There are match procedures that can be applied to data items.  A
;;; match procedure either accepts or rejects the data it is applied
;;; to.  Match procedures can be combined to apply to compound data
;;; items.

;;; A match procedure takes a list containing a data item, a
;;; dictionary, and a success continuation.  The dictionary
;;; accumulates the assignments of match variables to values found in
;;; the data.  The success continuation takes two arguments: the new
;;; dictionary, and the number of items absorbed from the list by the
;;; match.  If a match procedure fails it returns #f.

;;; Primitive match procedures:

(define (match:eqv pattern-constant)
  (define (eqv-match data dictionary succeed)
    (and (pair? data)
	 (eqv? (car data) pattern-constant)
	 (succeed dictionary 1)))
  eqv-match)

(define (match:element variable restrictions)
  (define (ok? datum)
    (every (lambda (restriction)
	     (restriction datum))
	   restrictions))
  (define (element-match data dictionary succeed)
    (and (pair? data)
	 (ok? (car data))
	 (let ((vcell (match:lookup variable dictionary)))
	   (if vcell
	       (and (equal? (match:value vcell) (car data))
		    (succeed dictionary 1))
	       (succeed (match:bind variable
				    (car data)
				    dictionary)
			1)))))
  element-match)


;;; Support for the dictionary.

(define (match:bind variable data-object dictionary)
  (cons (list variable data-object) dictionary))

(define (match:lookup variable dictionary)
  (assq variable dictionary))

(define (match:value vcell)
  (cadr vcell))

(define (match:segment variable)
  (define (segment-match data dictionary succeed)
    (and (list? data)
	 (let ((vcell (match:lookup variable dictionary)))
	   (if vcell
	       (let lp ((data data)
			(pattern (match:value vcell))
			(n 0))
		 (cond ((pair? pattern)
			(if (and (pair? data)
				 (equal? (car data) (car pattern)))
			    (lp (cdr data) (cdr pattern) (+ n 1))
			    #f))
		       ((not (null? pattern)) #f)
		       (else (succeed dictionary n))))
	       (let ((n (length data)))
		 (let lp ((i 0))
		   (if (<= i n)
		       (or (succeed (match:bind variable
						(list-head data i)
						dictionary)
				    i)
			   (lp (+ i 1)))
		       #f)))))))
  segment-match)

(define (match:list . match-combinators)
  (define (list-match data dictionary succeed)
    (and (pair? data)
	 (let lp ((lst (car data))
		  (matchers match-combinators)
		  (dictionary dictionary))
	   (cond ((pair? matchers)
		  ((car matchers)
		   lst
		   dictionary
		   (lambda (new-dictionary n)
		     (if (> n (length lst))
			 (error "Matcher ate too much."
				n))
		     (lp (list-tail lst n)
			 (cdr matchers)
			 new-dictionary))))
		 ((pair? lst) #f)
		 ((null? lst)
		  (succeed dictionary 1))
		 (else #f)))))
  list-match)

;;; Syntax of matching is determined here.

(define (match:element? pattern)
  (and (pair? pattern)
       (eq? (car pattern) '?)))

(define (match:segment? pattern)
  (and (pair? pattern)
       (eq? (car pattern) '??)))

(define (match:variable-name pattern) (cadr pattern))
(define (match:restrictions pattern) (cddr pattern))

(define (match:list? pattern)
  (and (list? pattern)
       (or (null? pattern)
	   (not (memq (car pattern) '(? ??))))))

(define match:->combinators
  (make-generic-operator 1 'eqv match:eqv))

(defhandler match:->combinators
  (lambda (pattern)
    (match:element
     (match:variable-name pattern)
     (match:restrictions pattern)))
  match:element?)

(defhandler match:->combinators
  (lambda (pattern) (match:segment (match:variable-name pattern)))
  match:segment?)

(defhandler match:->combinators
  (lambda (pattern)
    (apply match:list (map match:->combinators pattern)))
  match:list?)

(define (matcher pattern)
  (let ((match-combinator (match:->combinators pattern)))
    (lambda (datum)
      (match-combinator (list datum)
			'()
			(lambda (dictionary n)
			  (and (= n 1)
			       dictionary))))))

#|
(define (report-success dict n)
  (assert (= n 1))
  `(succeed ,dict))

((match:->combinators '(a ((? b) 2 3) 1 c))
 '((a (1 2 3) 1 c))
 '()
  report-success)
;Value: (succeed ((b 1)))

((match:->combinators '(a ((? b) 2 3) (? b) c))
 '((a (1 2 3) 2 c))
 '()
  report-success)
;Value: #f

((match:->combinators '(a ((? b) 2 3) (? b) c))
 '((a (1 2 3) 1 c))
 '()
  report-success)
;Value: (succeed ((b 1)))


((match:->combinators '(a (?? x) (?? y) (?? x) c))
 '((a b b b b b b c))
 '()
 (lambda (dict n)
   (assert (= n 1))
   (pp `(succeed ,dict))
   #f))
(succeed ((y (b b b b b b)) (x ())))
(succeed ((y (b b b b)) (x (b))))
(succeed ((y (b b)) (x (b b))))
(succeed ((y ()) (x (b b b))))
;Value: #f

((matcher '(a ((? b) 2 3) (? b) c))
 '(a (1 2 3) 1 c))
;Value: ((b 1))
|#

;;; Nice pattern inspection procedure that will be used by the
;;; pattern-directed invocation system.

(define (match:pattern-names pattern)
  (let loop ((pattern pattern) (names '()))
    (cond ((or (match:element? pattern)
               (match:segment? pattern))
           (let ((name
		  (match:variable-name pattern)))
             (if (memq name names)
                 names
                 (cons name names))))
          ((list? pattern)
           (let elt-loop
	       ((elts pattern) (names names))
             (if (pair? elts)
                 (elt-loop (cdr elts)
			   (loop (car elts) names))
                 names)))
          (else names))))

#|
 (match:pattern-names '((? a) (?? b)))
 ;Value: (b a)
|#
(define (make-pattern-operator #!optional rules)
  (define (operator self . arguments)
    (define (succeed value fail) value)
    (define (fail)
      (error "No applicable operations" self arguments))
    (try-rules arguments (entity-extra self) succeed fail))
  (make-entity operator (if (default-object? rules) '() rules)))

(define (attach-rule! operator rule)
  (set-entity-extra! operator
   (cons rule (entity-extra operator))))

;;; Pattern-directed factorial, with and without the rule macro.

#|
(define factorial (make-pattern-operator))

(attach-rule! factorial (rule '(0) 1))

(attach-rule! factorial
 (rule `((? n ,positive?))
       (* n (factorial (- n 1)))))

(factorial 10)
;Value: 3628800
|#

#|
(define factorial (make-pattern-operator))

(attach-rule! factorial
 (make-rule '((? n))
  (lambda (n) (* n (factorial (- n 1))))))

(attach-rule! factorial
 (make-rule '(0) (lambda () 1)))

(factorial 10)
;Value: 3628800
|#

#|
 (define quad
   (make-pattern-operator
    (list
     (rule 
      `((? a) (? b) (? c) (? x))
      (+ (* a (expt x 2))
	 (* b x)
	 c))

     (rule
      `((? a) (? x) (? x) + (? b) (? x) + (? c))
      (+ (* a (expt x 2))
	 (* b x)
	 c)))))

 (quad 1 2 3 4)
 ;Value: 27

 (quad 1 4 4 '+ 2 4 '+ 3)
 ;Value: 27
|#

#|
 (define frob
   (make-pattern-operator))

 (attach-rule! frob
  (rule
   '(a (?? x) (?? y) (?? x) c)
   (and (<= (length y) 2)
        y)))

 (apply frob '(a b b b b b b c))
 ;Value: (b b)
|#
MIT/GNU Scheme running under GNU/Linux
Type `^C' (control-C) followed by `H' to obtain information about interrupts.

Copyright (C) 2014 Massachusetts Institute of Technology
This is free software; see the source for copying conditions. There is NO
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

Image saved on Saturday May 17, 2014 at 2:39:25 AM
  Release 9.2 || Microcode 15.3 || Runtime 15.7 || SF 4.41 || LIAR/x86-64 4.118
  Edwin 3.116

1 ]=> (load "load")
;Loading "load.scm"...
;  Loading "ghelper.scm"... done
;  Loading "matcher.scm"... done
;  Loading "utils.scm"... done
;  Loading "rule-implementation.scm"... done
;  Loading "rules.scm"... done
;  Loading "pattern-operator.scm"... done
;... done
;Value: attach-rule!

1 ]=> (define group-axioms
   (list
    ;; Associative law of addition
    (rule '( (?? a) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) 1 (?? b))
	  `( ,@a  ,@b ))
    (rule '( (?? a) (?? c) (- ((?? c))) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) (- ((?? c))) (?? c) (?? b))
	  `( ,@a ,1 ,@b ))))
;Value: group-axioms

1 ]=> ;;(pp (try-rules '(a) assumptions 
;;	       (lambda (result fail)
;;	       (pp result)
;;		 )
;;	       (lambda () #f)
;;	       )) 

(define (try-push outcome start results)
	;;(pp "try to push")
	;;(pp results)
	(let* ((story (cons start (cadr (assoc start results))))
	       (n-story (length story))
		(old-vcell (assoc outcome results)))
	       (if old-vcell
		(let* ((old-story (cadr old-vcell))
		       (n-old-story (length old-story)))
		   (if (< n-story n-old-story)
			(cons (list outcome story) results)
			results))
		  
		  (cons (list outcome story) results))  ))
;Value: try-push

1 ]=> (define (deduce vars starters assumptions results)
  (define gen-assumptions
    (append 
     assumptions
  (let per-var ((vars  vars)
		(new-assumptions '())) 
	(if (pair? vars)
	  (per-var  (cdr vars) 
		   (cons (rule '( (?? a) 1 (?? b))
			       `( ,@a ,(car vars) (- ,(car vars)) ,@b ))
		    (cons
		     	(rule '( (?? a) 1 (?? b))
	  		`( ,@a (- ,(car vars)) ,(car vars) ,@b ))
		     new-assumptions)) )
	  new-assumptions
	 )	
    )))
  (let per-start ((starters starters)
		  (assumptions gen-assumptions)
		  (results results))
    	;;(pp "per-start")
	(if (pair? starters)
	  (let per-assumption ((start (car starters))
			(new-starters (cdr starters))
			(assumptions assumptions)
			(current-assumptions assumptions)
			(results results))
	    	;;(pp "per-assumption")
	    	(if (pair? current-assumptions)
		  ((car current-assumptions) start
				     (lambda (outcome f)
				     (per-assumption start new-starters assumptions (cdr current-assumptions ) (try-push outcome start results)))
				     (lambda () 
				      (per-assumption start new-starters assumptions (cdr current-assumptions ) results)))
		  (per-start new-starters assumptions results)))
	  results)))
;Value: deduce

1 ]=> #|
 (define hypothesis
   (list (rule '((?? x) a b (?? y)))
	 `( ,@x a c ,@y ))))

 (define hypothesis
	(list  (rule '( (?? a) (?? b) (? c))
	  `( ,@a r ,@b ,c))
	 (rule '((? c) (?? a) (?? b) )
	  `(,c ,@a r ,@b))

    (rule '( (?? a) r (?? b) (? c))
	  `( ,@a  ,@b ,c))
(rule '((? c) (?? a) r (?? b) )
	  `(,c ,@a  ,@b))

))

(define assumptions
   (append group-axioms hypothesis))

(define theorem
  '((b) (c))
  )
|#

(define (proof variables assumptions  theorem-start theorem-end)
  	
 	(let lp ((starters `(,theorem-start))
		(end theorem-end)
		(assumptions assumptions)
		(variables variables)
		(results `((,theorem-start ()))))
		(let* ((new-results (deduce variables starters assumptions results))
		       (vcell (assoc end results)))
			(if vcell
			  (cons end (cadr  vcell))
			  (lp (map car results) end assumptions variables new-results)
			  )
		)))
;Value: proof

1 ]=> (define (ppp lst)
  	(if (pair? lst)
	  (let ((new-lst (cdr lst)))
	    (ppp new-lst)
	    (pp (car lst))
	     )
	  (pp "Proved:"))
	  )
;Value: ppp

1 ]=> (ppp (proof '(a b c) group-axioms '(a b (- a b)) '(1))

End of input stream reached.
Moriturus te saluto.
MIT/GNU Scheme running under GNU/Linux
Type `^C' (control-C) followed by `H' to obtain information about interrupts.

Copyright (C) 2014 Massachusetts Institute of Technology
This is free software; see the source for copying conditions. There is NO
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

Image saved on Saturday May 17, 2014 at 2:39:25 AM
  Release 9.2 || Microcode 15.3 || Runtime 15.7 || SF 4.41 || LIAR/x86-64 4.118
  Edwin 3.116

1 ]=> (load "load")
;Loading "load.scm"...
;  Loading "ghelper.scm"... done
;  Loading "matcher.scm"... done
;  Loading "utils.scm"... done
;  Loading "rule-implementation.scm"... done
;  Loading "rules.scm"... done
;  Loading "pattern-operator.scm"... done
;... done
;Value: attach-rule!

1 ]=> (define group-axioms
   (list
    ;; Associative law of addition
    (rule '( (?? a) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) 1 (?? b))
	  `( ,@a  ,@b ))
    (rule '( (?? a) (?? c) (- (?? c)) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) (- (?? c)) (?? c) (?? b))
	  `( ,@a ,1 ,@b ))))
;Value: group-axioms

1 ]=> ;;(pp (try-rules '(a) assumptions 
;;	       (lambda (result fail)
;;	       (pp result)
;;		 )
;;	       (lambda () #f)
;;	       )) 

(define (try-push outcome start results)
	(pp "try to push")
	(pp outcome)
  	(pp results)
	(let* ((story (cons start (cadr (assoc start results))))
	       (n-story (length story))
		(old-vcell (assoc outcome results)))
	       (if old-vcell
		(let* ((old-story (cadr old-vcell))
		       (n-old-story (length old-story)))
		   (if (< n-story n-old-story)
			(cons (list outcome story) results)
			results))
		(cons (list outcome story) results)  )))
;Value: try-push

1 ]=> (define (deduce vars starters assumptions results)
  (define gen-assumptions
    (append 
     assumptions
  (let per-var ((vars  vars)
		(new-assumptions '())) 
	(if (pair? vars)
	  (per-var  (cdr vars) 
		   (cons (rule '( (?? a) 1 (?? b))
			       `( ,@a ,(car vars) (- ,(car vars)) ,@b ))
		    (cons
		     	(rule '( (?? a) 1 (?? b))
	  		`( ,@a (- ,(car vars)) ,(car vars) ,@b ))
		     new-assumptions)) )
	  new-assumptions
	 )	
    )))
  (let per-start ((starters starters)
		  (assumptions gen-assumptions)
		  (results results))
    	(pp "per-start")
	(if (pair? starters)
	  (let per-assumption ((start (car starters))
			(new-starters (cdr starters))
			(assumptions assumptions)
			(current-assumptions assumptions)
			(results results))
	    	(pp "per-assumption")
	    	(if (pair? current-assumptions)
		  ((car current-assumptions) start
				     (lambda (outcome f)
				     (per-assumption start new-starters assumptions (cdr current-assumptions ) (try-push outcome start results)))
				     (lambda () 
				      (per-assumption start new-starters assumptions (cdr current-assumptions ) results)))
		  (per-start new-starters assumptions results)))
	  results)))
;Value: deduce

1 ]=> (define hypothesis
   (list (rule '((?? x) a b (?? y))
	 `( ,@x a c ,@y ))))
;Value: hypothesis

1 ]=> (define assumptions
   (append group-axioms hypothesis))
;Value: assumptions

1 ]=> (define theorem
  '((a) (c))
  )
;Value: theorem

1 ]=> (define (proof variables assumptions  theorem-start theorem-end)
  	
 	(let lp ((starters `(,theorem-start))
		(end theorem-end)
		(assumptions assumptions)
		(variables variables)
		(results `((,theorem-start ()))))
		(let* ((new-results (deduce variables starters assumptions results))
		       (vcell (assoc end results)))
			(if vcell
			  (cadr vcell)
			  (lp (map car results) end assumptions variables new-results)
			  )
		)))
;Value: proof

1 ]=> (pp (proof '(a b c) assumptions '((- a) a c) '(c)))"per-start"
"per-assumption"
"try to push"
(1 (- a) a c)
((((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"try to push"
(1 c)
(((1 (- a) a c) (((- a) a c))) (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-start"
"per-start"
"per-assumption"
"try to push"
(1 (- a) a c)
(((1 c) (((- a) a c))) ((1 (- a) a c) (((- a) a c))) (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"try to push"
(1 c)
(((1 c) (((- a) a c))) ((1 (- a) a c) (((- a) a c))) (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-start"
"per-start"
"per-assumption"
"try to push"
(1 1 c)
(((1 c) (((- a) a c))) ((1 (- a) a c) (((- a) a c))) (((- a) a c) ()))
"per-assumption"
"try to push"
(c)
(((1 1 c) ((1 c) ((- a) a c))) ((1 c) (((- a) a c)))
                               ((1 (- a) a c) (((- a) a c)))
                               (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"try to push"
(c (- c) c)
(((c) ((1 c) ((- a) a c))) ((1 1 c) ((1 c) ((- a) a c)))
                           ((1 c) (((- a) a c)))
                           ((1 (- a) a c) (((- a) a c)))
                           (((- a) a c) ()))
"per-assumption"
"try to push"
((- c) c c)
(((c (- c) c) ((1 c) ((- a) a c))) ((c) ((1 c) ((- a) a c)))
                                   ((1 1 c) ((1 c) ((- a) a c)))
                                   ((1 c) (((- a) a c)))
                                   ((1 (- a) a c) (((- a) a c)))
                                   (((- a) a c) ()))
"per-assumption"
"try to push"
(b (- b) c)
((((- c) c c) ((1 c) ((- a) a c))) ((c (- c) c) ((1 c) ((- a) a c)))
                                   ((c) ((1 c) ((- a) a c)))
                                   ((1 1 c) ((1 c) ((- a) a c)))
                                   ((1 c) (((- a) a c)))
                                   ((1 (- a) a c) (((- a) a c)))
                                   (((- a) a c) ()))
"per-assumption"
"try to push"
((- b) b c)
(((b (- b) c) ((1 c) ((- a) a c))) (((- c) c c) ((1 c) ((- a) a c)))
                                   ((c (- c) c) ((1 c) ((- a) a c)))
                                   ((c) ((1 c) ((- a) a c)))
                                   ((1 1 c) ((1 c) ((- a) a c)))
                                   ((1 c) (((- a) a c)))
                                   ((1 (- a) a c) (((- a) a c)))
                                   (((- a) a c) ()))
"per-assumption"
"try to push"
(a (- a) c)
((((- b) b c) ((1 c) ((- a) a c))) ((b (- b) c) ((1 c) ((- a) a c)))
                                   (((- c) c c) ((1 c) ((- a) a c)))
                                   ((c (- c) c) ((1 c) ((- a) a c)))
                                   ((c) ((1 c) ((- a) a c)))
                                   ((1 1 c) ((1 c) ((- a) a c)))
                                   ((1 c) (((- a) a c)))
                                   ((1 (- a) a c) (((- a) a c)))
                                   (((- a) a c) ()))
"per-assumption"
"try to push"
((- a) a c)
(((a (- a) c) ((1 c) ((- a) a c))) (((- b) b c) ((1 c) ((- a) a c)))
                                   ((b (- b) c) ((1 c) ((- a) a c)))
                                   (((- c) c c) ((1 c) ((- a) a c)))
                                   ((c (- c) c) ((1 c) ((- a) a c)))
                                   ((c) ((1 c) ((- a) a c)))
                                   ((1 1 c) ((1 c) ((- a) a c)))
                                   ((1 c) (((- a) a c)))
                                   ((1 (- a) a c) (((- a) a c)))
                                   (((- a) a c) ()))
"per-assumption"
"per-start"
"per-assumption"
"try to push"
(1 1 (- a) a c)
(((a (- a) c) ((1 c) ((- a) a c))) (((- b) b c) ((1 c) ((- a) a c)))
                                   ((b (- b) c) ((1 c) ((- a) a c)))
                                   (((- c) c c) ((1 c) ((- a) a c)))
                                   ((c (- c) c) ((1 c) ((- a) a c)))
                                   ((c) ((1 c) ((- a) a c)))
                                   ((1 1 c) ((1 c) ((- a) a c)))
                                   ((1 c) (((- a) a c)))
                                   ((1 (- a) a c) (((- a) a c)))
                                   (((- a) a c) ()))
"per-assumption"
"try to push"
((- a) a c)
(((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"try to push"
(1 1 c)
(((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"try to push"
(c (- c) (- a) a c)
(((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- c) c (- a) a c)
(((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(b (- b) (- a) a c)
((((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- b) b (- a) a c)
(((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(a (- a) (- a) a c)
((((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- a) a (- a) a c)
(((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-start"
"per-assumption"
"try to push"
(1 (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"try to push"
(1 c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-start"
"per-start"
"per-assumption"
"try to push"
(1 1 c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"try to push"
(c (- c) c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- c) c c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(b (- b) c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- b) b c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(a (- a) c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-start"
"per-assumption"
"try to push"
(1 1 (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"try to push"
(1 1 c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"try to push"
(c (- c) (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- c) c (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(b (- b) (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- b) b (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
(a (- a) (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"try to push"
((- a) a (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-start"
"per-assumption"
"try to push"
(1 (- a) a c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"try to push"
(1 c)
((((- a) a (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- b) b (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((b (- b) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 (((- c) c (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((c (- c) (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((1 1 (- a) a c) ((1 (- a) a c) ((- a) a c)))
 ((a (- a) c) ((1 c) ((- a) a c)))
 (((- b) b c) ((1 c) ((- a) a c)))
 ((b (- b) c) ((1 c) ((- a) a c)))
 (((- c) c c) ((1 c) ((- a) a c)))
 ((c (- c) c) ((1 c) ((- a) a c)))
 ((c) ((1 c) ((- a) a c)))
 ((1 1 c) ((1 c) ((- a) a c)))
 ((1 c) (((- a) a c)))
 ((1 (- a) a c) (((- a) a c)))
 (((- a) a c) ()))
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-assumption"
"per-start"
((1 c) ((- a) a c))
;Unspecified return value

1 ]=> 
End of input stream reached.
Moriturus te saluto.
(declare (usual-integrations))

;;; A rule is a procedure constructed from a pattern and a consequent
;;; procedure.  A rule takes data that the rule may apply to and a
;;; success and failure continuation.  The consequent procedure binds
;;; the variables named in the pattern.  It produces the result of the
;;; rule as a function of the values of those variables that matched
;;; the data presented.

(define (make-rule pattern consequent)
  (let ((match-procedure (match:->combinators pattern))
	(bound-variables (procedure-bound-variables consequent)))
    (define (the-rule data succeed fail)
      (or (match-procedure (list data) '()
 	    ;; A matcher-success continuation
	    (lambda (dict n)
	      (define (matched-value name)
		(match:value
		 (or (match:lookup name dict)
		     (error "Handler asked for unknown name"
			    name dict))))
	      (and (= n 1)
		   (let ((result
			  (apply consequent
				 (map matched-value
				      bound-variables))))
		     (and result
			  (succeed result
				   (lambda () #f)))))))
	  (fail)))
    the-rule))

(define-syntax rule
  (sc-macro-transformer
   (lambda (form use-env)
     (let ((pattern (cadr form))
	   (handler-body (caddr form)))
       `(make-rule 
	 ,(close-syntax pattern use-env)
	 ,(compile-handler handler-body use-env
			   (match:pattern-names pattern)))))))

(define (compile-handler form env names)
  ;; See magic in utils.scm
  (make-lambda names env
    (lambda (env*) (close-syntax form env*))))

#|
(pp (syntax '(rule '(* (? a) (? b))
		   (and (expr<? a b)
			`(* ,a ,b)))
	    (the-environment)))

; (make-rule '(* (? a) (? b))
;  (lambda (b a)
;    (and (expr<? a b)
;         (list '* a b))))
;Unspecified return value
|#
;;;; File:  rules.scm -- Example of algebraic simplification

;;; This is the essence of a simplifier.  It recursively simplifies
;;; subexpressions and then simplifies the enclosing expression.


(define (rule-simplifier the-rules)
  (define (simplify-expression expression)
    (let ((subexpressions-simplified
	   (if (list? expression)
	       (map simplify-expression expression)
	       expression)))
      ;; Once the subexpressions are simplified we 
      ;; resimplify the expression that contains them.
      (try-rules subexpressions-simplified the-rules
       ;; If any rule applies we must resimplify.
       (lambda (result fail)
	 (simplify-expression result))
       ;; If no rule applies we are done.
       (lambda ()
	 subexpressions-simplified))))
  ;; rule-memoize is just an identity, unless we 
  ;; want to make sure that expressions are 
  ;; simplified only once.
  (rule-memoize simplify-expression))


;;; Try rules executes each rule on the data.  
;;; If a rule is found applicable the success
;;; continuation is called.  If a rule is found
;;; inapplicable the next rule is tried.

(define (try-rules data rules succeed fail)
  (let per-rule ((rules rules))
    (if (null? rules)
	(fail)
	((car rules) data
		     succeed
		     (lambda ()
		       (per-rule (cdr rules)))))))


;;; A simple set of rules.

(define algebra-1
  (rule-simplifier
   (list
    ;; Associative law of addition
    (rule '(+ (? a) (+ (? b) (? c)))
	  `(+ (+ ,a ,b) ,c))

    ;; Commutative law of multiplication
    (rule '(* (? b) (? a))
	  (and (expr<? a b)
	       `(* ,a ,b)))

    ;; Distributive law of multiplication over addition
    (rule '(* (? a) (+ (? b) (? c)))
	  `(+ (* ,a ,b) (* ,a ,c))) )))

(define (list<? x y)
  (let ((nx (length x)) (ny (length y)))
    (cond ((< nx ny) #t)
	  ((> nx ny) #f)
	  (else
	   (let lp ((x x) (y y))
	     (cond ((null? x) #f)	; same
		   ((expr<? (car x) (car y)) #t)
		   ((expr<? (car y) (car x)) #f)
		   (else (lp (cdr x) (cdr y)))))))))

(define expr<?
  (make-entity
   (lambda (self x y)
     (let per-type ((types (entity-extra self)))
       (if (null? types)
	   (error "Unknown expression type -- expr<?" x y)
	   (let ((predicate? (caar types))
		 (comparator (cdar types)))
	     (cond ((predicate? x)
		    (if (predicate? y)
			(comparator x y)
			#t))
		   ((predicate? y) #f)
		   (else (per-type (cdr types))))))))
   `((,null?   . ,(lambda (x y) #f))
     (,number? . ,<)
     (,symbol? . ,symbol<?)
     (,list?   . ,list<?))))
#|
 (algebra-1 '(* (+ y (+ z w)) x))
 ;Value: (+ (+ (* x y) (* x z)) (* w x))
|#

(define algebra-2
  (rule-simplifier
   (list

    ;; Sums

    (rule `(+ (? a)) a)

    (rule `(+ (?? a) (+ (?? b)) (?? c))
	  `(+ ,@a ,@b ,@c))

    (rule `(+ (?? a) (? y) (? x) (?? b))
	  (and (expr<? x y)
	       `(+ ,@a ,x ,y ,@b)))
    

    ;; Products

    (rule `(* (? a)) a)

    (rule `(* (?? a) (* (?? b)) (?? c))
	  `(* ,@a ,@b ,@c))

    (rule `(* (?? a) (? y) (? x) (?? b))
	  (and (expr<? x y)
	       `(* ,@a ,x ,y ,@b)))


    ;; Distributive law

    (rule `(* (?? a) (+ (?? b)) (?? c))
	  `(+ ,@(map (lambda (x) `(* ,@a ,x ,@c)) b)))


    ;; Numerical simplifications below

    (rule `(+ 0 (?? x)) `(+ ,@x))

    (rule `(+ (? x ,number?) (? y ,number?) (?? z))
	  `(+ ,(+ x y) ,@z))


    (rule `(* 0 (?? x)) 0)
     
    (rule `(* 1 (?? x)) `(* ,@x))

    (rule `(* (? x ,number?) (? y ,number?) (?? z))
	  `(* ,(* x y) ,@z))

    )))

#|
 (algebra-2 '(* (+ y (+ z w)) x))
 ;Value: (+ (* w x) (* x y) (* x z))

 (algebra-2 '(+ (* 3 (+ x 1)) -3))
 ;Value: (* 3 x)
|#
(((1 a) ((a))) ((a) ()))
(((1 1 a) ((1 a) (a))) ((1 a) ((a))) ((a) ()))
;;; utils.scm -- Hairy utility functions for implementing the special
;;; rule syntax for pattern-directed invocation.
;;;


(declare (usual-integrations))

;;; This procedure was dredged from the dark recesses of Edwin.  Many
;;; computer scientists would claim that it should never have been
;;; allowed to see the light of day.

(define (procedure-bound-variables proc #!optional default-argl)
  "Returns the arg list of PROC.
   Grumbles if PROC is an undocumented primitive."
  (if (primitive-procedure? proc)
      (let ((doc-string
	     (primitive-procedure-documentation proc)))
	(if doc-string
	    (let ((newline
		   (string-find-next-char doc-string #\newline)))
	      (if newline
		  (string-head doc-string newline)
		  doc-string))
	    (string-append
	     (write-to-string proc)
	     " has no documentation string.")))
      (let ((code (procedure-lambda proc)))
	(if code
	    (lambda-components* code
	      (lambda (name required optional rest body)
		name body
		(append required
		 (if (null? optional) '() `(#!OPTIONAL ,@optional))
		 (if rest `(#!REST ,rest) '()))))
	    (if (default-object? default-argl)
		"No debugging information available for this procedure."
		default-argl)))))

;;; Magic!

(define (make-lambda bvl use-env generate-body)
  (capture-syntactic-environment
   (lambda (transform-env)
     (close-syntax
      `(,(close-syntax 'lambda transform-env)
	,bvl
	,(capture-syntactic-environment
	  (lambda (use-env*)
	    (close-syntax (generate-body use-env*)
			  transform-env))))
      use-env))))
