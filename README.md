
## Grouptheory-Isabelle
As part of our cryptography/math/comp-sci course at the DSA 2024 we were tasked with creating our own definition of groups within Isabelle, following the definitions of Van der Vaerden in his 1955 publication "Algebra"[^1].
Our formalization ended up being something in between the two existing definitions within Isabelle [^2] [^3], using a mixture of records and locales[^4] and skipping the definition of magmas, semigroups and monoids.

### Shortcomings:
The Product presented is thus more compact, but lacks some of the features of the other existing formalizations - namely powers, subgroups and homo-/isomorphisms. 

### Documentation:
Documentation and a gentle introduction to group theory can be found at github.com/sariaki/Grouptheory-Docs/main. (to be released)

### Credits:
- [Paul B.](https://github.com/sariaki) 
- [Mars F.](https://github.com/marsx133)

### References/Further Reading:
[^1]: Nipkow, Paulson, Wenzel: Isabelle/HOL: A Proof Assistant for Higher-Order Logic (2002)
[^2]: https://www.isa-afp.org/browser_info/devel/HOL/HOL-Algebra/Group.html
[^3]: https://isabelle.in.tum.de/library/HOL/HOL/Groups.html
[^4]: Van der Waerden: Algebra (1955)
