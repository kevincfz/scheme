(define count lst
	(if (null? lst) 0
		(+ 1 count(cdr lst)))
)


; tail recursion
(define (count-tail lst)
	(define (helper lst num)
		(if (null? lst) 
			num
			(helper (cdr lst) (+ 1 num))))
 (helper lst 0))


;tail factorial
(define (tail-fact n)
	(define (helper n result)
		(if (= n 0)
			result
			(helper (- n 1) (* result n) )))
	(helper n 1))



;tail append
(define (append-tail l1 l2)
	(define (helper l1 l2)
			(if (null? l1)
				l2
				(helper (cdr l1) (cons (car l1) (l2)))
(helper (tail-reverse a) b)
		)))


	



;scoping 
(define a (lambda (f x) (f(f(x)))))




