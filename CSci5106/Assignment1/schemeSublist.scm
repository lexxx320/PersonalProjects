(define (removeK list k)
  (define (helper list k firstPart)
  (if (null? list) list
      (if (= k 1) (append firstPart (cdr list))
          (helper(cdr list) (- k 1) (cons (car list) firstPart))
          )
      )
    )
  (helper list k '())
  )

(define (sublist listA listB)
  (define (sublistHelper listA listB tempListB k)
    (if (null? tempListB) #f
        (if (= (car listA) (car tempListB)) (sublist (cdr listA) (removeK listB k))
            (sublistHelper listA listB (cdr tempListB) (+ k 1))
            )
        )
    )   
  (if (null? listA) #t
      (if (null? listB) #f
          (sublistHelper listA listB listB 1)
          )
      )
  )
        
        
        
  (sublist '(1 2 3 4) '(1 2 3 3 4 5))
  (sublist '(1 1 1 1 1) '(1))
  (sublist '(1 2 3 4) '(1 2 3 4))
  (sublist '(1 2) '(1 2 3))
  (sublist '(1 2) '(1 2 2 2 2))



          