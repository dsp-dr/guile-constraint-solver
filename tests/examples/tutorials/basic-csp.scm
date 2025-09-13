#!/usr/bin/env guile
!#

;;; tutorials/basic-csp.scm --- Basic CSP tutorial and examples

(add-to-load-path (dirname (dirname (dirname (dirname (current-filename))))))

(use-modules (core constraint-engine)
             (problems n-queens)
             (problems sudoku)
             (problems change-making)
             (ice-9 format))

(define (tutorial-intro)
  (display "=== Guile Constraint Solver Tutorial ===\n\n")
  (display "This tutorial demonstrates three constraint solving approaches:\n")
  (display "1. Native CSP with backtracking and constraint propagation\n")
  (display "2. Z3 SMT solver integration\n")
  (display "3. Dynamic programming (where applicable)\n\n"))

(define (demo-simple-csp)
  (display "=== Simple CSP Example ===\n")
  (display "Variables: X, Y, Z with domains {1,2,3}\n")
  (display "Constraints: X ≠ Y, Y ≠ Z, X + Y + Z = 6\n\n")

  (let* ((x (make-variable 'x (make-domain '(1 2 3))))
         (y (make-variable 'y (make-domain '(1 2 3))))
         (z (make-variable 'z (make-domain '(1 2 3))))
         (variables (list x y z))
         (constraints
          (list
           ;; X ≠ Y
           (make-constraint (list x y)
             (lambda (x-val y-val) (not (= x-val y-val))))
           ;; Y ≠ Z
           (make-constraint (list y z)
             (lambda (y-val z-val) (not (= y-val z-val))))
           ;; X + Y + Z = 6
           (sum-constraint (list x y z) 6))))

    (let ((solution (solve-csp variables constraints)))
      (if solution
          (begin
            (display "Solution found: ")
            (for-each (lambda (var-val)
                        (format #t "~a=~a " (car var-val) (cdr var-val)))
                      solution)
            (newline))
          (display "No solution found\n")))
    (newline)))

(define (demo-n-queens)
  (display "=== N-Queens Problem (4x4) ===\n")
  (display "Place 4 queens on a 4x4 chessboard so none attack each other\n\n")

  (let ((solution (n-queens-csp 4)))
    (if solution
        (print-chessboard solution 4)
        (display "No solution found\n")))
  (newline))

(define (demo-change-making)
  (display "=== Coin Change Problem ===\n")
  (display "Make 37 cents with coins {10, 9, 1}\n\n")

  (let* ((total 37)
         (coins '(10 9 1)))

    ;; Dynamic Programming
    (display "Dynamic Programming Solution:\n")
    (let ((solution (make-change-dp total coins)))
      (if solution
          (format #t "  Coins: ~a (total: ~a coins)\n"
                  solution (length solution))
          (display "  No solution found\n")))

    ;; Z3 SMT
    (display "\nZ3 SMT Solver Solution:\n")
    (let ((result (make-change-z3 total coins)))
      (if result
          (format #t "  ~a\n" result)
          (display "  No solution found\n"))))
  (newline))

(define (performance-comparison)
  (display "=== Performance Comparison ===\n")
  (display "Comparing solving times for different approaches...\n\n")

  ;; Time N-Queens CSP
  (display "4-Queens CSP: ")
  (let ((start (current-time)))
    (n-queens-csp 4)
    (let ((elapsed (- (current-time) start)))
      (format #t "~a seconds\n" elapsed)))

  ;; Time Change Making DP
  (display "Change Making DP: ")
  (let ((start (current-time)))
    (make-change-dp 37 '(10 9 1))
    (let ((elapsed (- (current-time) start)))
      (format #t "~a seconds\n" elapsed)))

  (newline))

(define (main)
  (tutorial-intro)
  (demo-simple-csp)
  (demo-n-queens)
  (demo-change-making)
  (performance-comparison)
  (display "Tutorial complete! Try experimenting with different problems.\n"))

(main)