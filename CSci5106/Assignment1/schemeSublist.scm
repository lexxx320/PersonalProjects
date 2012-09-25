;This function looks at three different cases
;Case1: First list is empty, return true
;Case2: Else if second list is empty, return false
;Case3: Neither are empty then,
;If the first element in listA is equal to the first
;element in list b, then check for the rest of the list
;If not, then restart listA and check against the rest of listB

  (define (sublist listA listB)
    (define (helper listA origListA listB)
      (if (null? listA) #t
          (if (null? listB) #f
              (if (= (car listA) (car listB)) (helper (cdr listA) origListA (cdr listB))
                  (helper origListA origListA (cdr listB))
                  )
              )
          )
      )
    (helper listA listA listB)
    )
        
  (sublist '(1 2 3 4) '(1 2 3 3 1 2 3 4 1 2))
  (sublist '(1 2) '(32 1 2 1))
  (sublist '(1 2 3 4) '(1 2 5 3 4))
  (sublist '(1 2) '(1 2 3))
  (sublist '(1 2) '(1 2 2 2 2))



          