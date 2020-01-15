(define map
  (let ((null? null?)
	(car car) (cdr cdr)
	(cons cons) (apply apply))
    (letrec ((map-loop (lambda (f l . ls)
		     (if (null? l)
			 '() ; simplifying assumption: if l is empty, then ls is also empty
			 (if (null? ls)
			     (cons (f (car l)) (map-loop f (cdr l)))
			     (cons (apply f (car l) (map-loop car ls))
				   (apply map f (cdr l) (map-loop cdr ls))))))))
      map-loop)))

(define fold-left
	(let ((null? null?)
	  (car car) (cdr cdr)
	  (apply apply) (map map))
		(letrec ((fold-loop (lambda (f acc l . ls)
				(if(null? l)
				acc
				(if(null? ls)
					(fold-loop f (f acc (car l)) (cdr l) )
					(apply fold-loop f (apply f acc (car l) (map car ls))
									   (cdr l)
									   (map cdr ls) ) )))))
		fold-loop)))

(define fold-right
	(let ((null? null?)
	  (car car) (cdr cdr)
	  (apply apply) (map map))
		(letrec ((auxAppend (lambda (l1 l2)
					(if (null? l1)
					l2
					(cons (car l1) (auxAppend (cdr l1) l2)))))
				(fold-loop (lambda (f acc l . ls)
					(if(null? l)
					acc
					(if(null? ls)
						(f (car l) (fold-loop f acc (cdr l)))
						(apply f (car l)
							(auxAppend	(map car ls)
										(cons (apply fold-loop f acc (cdr l) (map cdr ls)) '() )) )
						)))))
		fold-loop)))

(define cons*
	(let ((null? null?) (car car) (cdr cdr)
		  (fold-right fold-right) (cons cons))
			(letrec	((last (lambda (l)
							(if (null? l)
							l
							(if (null? (cdr l))
								(car l)
								(last (cdr l))))))
					(exceptLast (lambda (l)
							(if (null? l)
							l
							(if (null? (cdr l))
								'()
								(cons (car l) (exceptLast (cdr l)))))))
					(cons-impl (lambda args
						(if (null? args)
						args
						(if (null? (cdr args))
							(car args)
							(fold-right cons (last args) (exceptLast args)))))))
	cons-impl)))

(define append
  (let ((null? null?)
	(fold-right fold-right)
	(cons cons))
    (lambda args
      (fold-right (lambda (e a)
		    (if (null? a)
			e
			(fold-right cons a e)))
		  '() args))))

(define list (lambda x x))

(define list?
  (let ((null? null?)
	(pair? pair?)
	(cdr cdr))
    (letrec ((list?-loop (lambda (x)
			   (or (null? x)
			       (and (pair? x)
				    (list? (cdr x)))))))
      list?-loop)))

(define length
  (let ((fold-left fold-left)
	(+ +))
    (lambda (l)
      (fold-left (lambda (acc e) (+ acc 1)) 0 l))))

(define make-string
  (let ((null? null?) (car car)
	(make-string make-string))
    (lambda (x . y)
      (if (null? y)
	  (make-string x #\nul)
	  (make-string x (car y))))))

(define not
  (lambda (x) (if x #f #t)))

(define number?
  (let ((float? float?)
	(integer? integer?))
    (lambda (x)
      (or (float? x) (integer? x)))))

(define +
  (let ((fold-left fold-left)
	(+ +))
    (lambda x (fold-left + 0 x))))

(define *
  (let ((fold-left fold-left)
	(* *))
    (lambda x (fold-left * 1 x))))

(define -
  (let ((apply apply)
	(- -) (+ +)
	(null? null?))
    (lambda (x . y)
      (if (null? y)
	  (- 0 x)
	  (- x (apply + y))))))

(define /
  (let ((apply apply)
	(/ /) (* *)
	(null? null?))
    (lambda (x . y)
      (if (null? y)
	  (/ 1 x)
	  (/ x (apply * y))))))

(define =
  (let ((= =) (null? null?)
	(car car) (cdr cdr)
	(apply apply))
    (letrec ((=-loop (lambda (x . y)
		       (if (null? y)
			   #t ; simplifying assumption: x is a number
			   (and (= x (car y)) (apply =-loop x (cdr y)))))))
      =-loop)))

(define <
  (let ((null? null?) (< <)
	(car car) (cdr cdr))
    (letrec ((<-loop (lambda (element lst)
		     (if (null? lst)
			 #t
			 (and (< element (car lst))
			     (<-loop (car lst) (cdr lst)))))))
      (lambda (x . y)
	(<-loop x y)))))

(define >
  (let ((null? null?) (< <) (= =)
	(not not) (car car) (cdr cdr))
    (letrec ((>-loop (lambda (element lst)
		     (if (null? lst)
			 #t
			 (and (not (or
				    (< element (car lst))
				    (= element (car lst))))
			      (>-loop (car lst) (cdr lst)))))))
      (lambda (x . y)
	(>-loop x y)))))

(define zero?
  (let ((= =))
    (lambda (x) (= x 0))))

(define string->list
  (let ((string-ref string-ref)
	(string-length string-length)
	(< <) (- -))
    (lambda (s)
      (letrec ((s->l-loop (lambda (n a)
			    (if (< n 0)
				a
				(s->l-loop (- n 1) (cons (string-ref s n) a))))))
	(s->l-loop (- ( s) 1) '())))))

(define equal?
  (let ((= =) (string->list string->list)
	(integer? integer?) (float? float?)
	(pair? pair?) (char? char?)
	(string? string?) (eq? eq?)
	(car car) (cdr cdr)
	(char->integer char->integer))
    (letrec ((equal?-loop (lambda (x y)
			    (or
			     (and (integer? x) (integer? y) (= x y))
			     (and (float? x) (float? y) (= x y))
			     (and (pair? x) (pair? y) (equal?-loop (car x) (car y)) (equal?-loop (cdr x) (cdr y)))
			     (and (char? x) (char? y) (= (char->integer x) (char->integer y)))
			     (and (string? x) (string? y) (equal?-loop (string->list x) (string->list y)))
			     (eq? x y)))))
    equal?-loop)))
