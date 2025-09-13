#!/usr/bin/env guile
#!/usr/bin/env guile
!#

(add-to-load-path (dirname (dirname (current-filename))))

(use-modules (problems change-making)
             (ice-9 format))

(define (run-change-example)
  (let* ((coins '(10 9 1))
         (total 37))
    (format #t "=== Change Making Problem ===\n")
    (format #t "Making ~a cents with coins ~a\n\n" total coins)
    
    ;; Dynamic Programming
    (format #t "1. Dynamic Programming Solution:\n")
    (let ((solution (make-change-dp total coins)))
      (format #t "   Solution: ~a (total: ~a coins)\n\n" 
              solution (length solution)))
    
    ;; Z3 Solver
    (format #t "2. Z3 SMT Solver Solution:\n")
    (let ((result (make-change-z3 total coins)))
      (if result
          (format #t "   ~a\n\n" result)
          (format #t "   No solution found\n\n")))
    
    ;; Native CSP
    (format #t "3. Native CSP Solution:\n")
    (let ((result (make-change-csp total coins 10)))
      (if result
          (format #t "   ~a\n" result)
          (format #t "   No solution found\n")))))

(run-change-example)
