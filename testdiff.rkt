#lang racket
(require "dynanal.rkt")
(require "dynanal_newclosure.rkt")
(require test-engine/racket-tests)

(check-expect (test-old) (test-new))
(test)