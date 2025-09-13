(use-modules (srfi srfi-64)
             (problems change-making))

(test-begin "change-making")

(test-equal "DP solution for article example"
  4
  (length (make-change-dp 37 '(10 9 1))))

(test-equal "DP solution for simple case"
  2
  (length (make-change-dp 6 '(1 3 4))))

(test-assert "Z3 finds solution"
  (make-change-z3 37 '(10 9 1)))

(test-end "change-making")
