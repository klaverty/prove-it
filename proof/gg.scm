(load "load")

  (define group-axioms
   (list
    ;; It exists an identity with the following property
    (rule '( (?? a) (?? b))
	  `( ,@a ,1 ,@b ))
    (rule '( (?? a) 1 (?? b))
	  `( ,@a  ,@b ))
    ;; For any element c, it exists an inverse of c (we will call  this (-c))
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
  
  ;; Generate the extra assumptions induced by the free variable that we are using
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

  ;;Iterate over the set of inference rules and derive from the current set of true theorems (starters) a new set of true theorems (new-starters). Then it recurse over new-starters.
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
	  (pp "Proved:")))


#|
(ppp (proof '(a b c) assumptions '(b) '(c) ))
"Proved:"
(b)
(1 b)
((- a) a b)
((- a) a c)
(1 c)
(c)
|#


;;(ppp (proof '(a b) assumptions '(b) '(c)))

#|
(ppp (proof '(a b) group-axioms '((- a b)) '((- b) (- a))))
"Proved:"
((- a b))
(1 (- a b))
(1 1 (- a b))
((- b) b 1 (- a b))
((- b) b (- b) b (- a b))
((- b) 1 b (- a b))
((- b) (- a) a b (- a b))
((- b) (- a) 1)
((- b) (- a))
|#

;;(ppp (proof '(r) assumptions '(r) '(1)))
;;
;(pp (proof '(a b c) assumptions '(b) '(c) ))
