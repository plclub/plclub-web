---
title: "Petr4: Formal Foundations for P4 Data Planes"
speaker: "Nate Foster"
semester: "FA20"
---

Abstract: P4 is a domain-specific language for specifying the behavior of packet-processing systems. It is based on an elegant design with high-level abstractions, such as parsers and match action pipelines, that can be compiled to efficient implementations in hardware or software. Unfortunately, like many industrial languages, P4 lacks a formal foundation. The P4 specification is a 160-page document with a mixture of informal prose, graphical diagrams, and pseudocode. The reference compiler is complex, running to over 40KLoC of C++ code. Neither of these artifacts is suitable for formal reasoning. 

This talk will introduce a new framework called Petr4 (pronounced "Petra"), that puts P4 on a solid foundation. Petr4 uses standard elements of the semantics engineering toolkit, namely type systems and operational semantics, to build a compositional semantics that assigns an unambiguous meaning to every P4 program. Petr4 is implemented as an OCaml prototype that has been validated against a suite of over 750 tests from the reference implementation. While developing Petr4, we discovered dozens of bugs in the language specification and the reference implementation, many of which have been fixed. Furthermore, we have used Petr4 to establish the soundness of P4’s type system, prove key properties such as termination, and formalize a language extension.

Petr4 is joint work with Ryan Donges (Cornell), Mina Tahbasbi Arashloo (Cornell), Santiago Bautista (ENS Rennes), Alexander Chang (Cornell), Newton Ni (Cornell), Samwise Parkinson (Cornell), Rudy Peterson (Cornell), Alaia Solko Breslin (Cornell) and Amanda Xu (Cornell), and will (conditionally) appear at POPL '21.

Biography: Nate Foster is an Associate Professor at Cornell University; a Principal Research Engineer at Barefoot Networks, an Intel Company; and a member of the Penn PLClub Alumni Association.
