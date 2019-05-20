#;"testout:hello\nbutter\npeanut\n()\n"
#lang racket
(void
 (write-string "hello\n")
 (write-string "butter\n" (current-error-port))
 (write-string "peanut\n" (current-output-port)))
