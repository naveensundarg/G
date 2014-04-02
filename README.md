
#**G**

**G** is a natural deduction style theorem prover in the style of Pollock's Oscar. 

__Rationale__:

> A few years ago, Geoff Sutcliffe, one of the founders of the TPTP library (Thousands of problems for theorem provers) issued a challenge to OSCAR. At CADE-13, a competition was held for clausal-form theorem provers. Otter was one of the most successful contestants. In addition, Otter is able to handle problems stated in natural form (as opposed to clausal form), and Otter is readily available for different platforms. Sutcliffe selected 212 problems from the TPTP library, and suggested that OSCAR and Otter run these problems on the same hardware. This Shootout at the ATP corral took place, with the result that OSCAR was on the average 40 times faster than Otter. In addition, OSCAR was able to find proofs for 16 problems on which Otter failed, and Otter was able to find proofs for only 3 problems on which OSCAR failed. Taking into account that Otter was written in C and OSCAR in LISP, the speed difference of the algorithms themselves could be as much as an order of magnitude greater. (Pollock 2008) 

> Pollock, John L. 2008. “OSCAR: An Architecture for Generally Intelligent Agents.” Frontiers in Artificial Intelligence and Applications 171:275–286.

## To get started 

    (load "loader.lisp")
  
## Run all the tests

    (run-all-tests nil)
  
## Get started with proving

    (prove list-of-premises goal)
    (prove '() '(or p (not p)))

## Status
   Passes all propositional tests (save for one) in 
   [Seventy-Five Problems for Testing Automatic Theorem Provers ](http://webloria.loria.fr/~areces/cordoba08/Bib/75ATPproblems86.pdf)

## Prerequisites 
   Quicklisp (to install cl-unification)
