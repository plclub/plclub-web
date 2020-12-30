---
title: "A Constructive Model of Directed Univalence of Bicubical Sets"
speaker: "Matthew Weaver"
semester: "FA20"
---

Abstract: Directed type theory is an analogue of homotopy type theory where types represent categories, generalizing groupoids. A bisimplicial approach to directed type theory, developed by Riehl and Shulman, is based on equipping each type with both a notion of path and a separate notion of directed morphism. In this setting, a directed analogue of the univalence axiom asserts that there is a universe of covariant discrete fibrations whose directed morphisms correspond to functions—a higher-categorical analogue of the category of sets and functions. In this work, we give a constructive model of a directed type theory with directed univalence in bicubical, rather than bisimplicial, sets. We formalize much of this model using Agda as the internal language of a 1-topos, following Orton and Pitts. First, building on the cubical techniques used to give computational models of homotopy type theory, we show that there is a universe of covariant discrete fibrations, with a partial directed univalence principle asserting that functions are a retract of morphisms in this universe. To complete this retraction into an equivalence, we refine the universe of covariant fibrations using the constructive sheaf models by Coquand, Ruch and Sattler. In this talk, I will focus on what programming and verification using bicubical directed type theory will look like in the future. (Joint work with Dan Licata)

Homework: Let’s consider defining the untyped lambda calculus with scoped variables (shown below in Agda notation): 

data Ctx : Type where

  ∙   : Ctx

  ext : Ctx → Ctx



Var : Ctx → Type

Var ∙       = ⊥

Var (ext Γ) = (Var Γ) + ⊤



data Tm (Γ : Ctx) : Type where

  var : Var Γ → Tm Γ

  app : Tm Γ → Tm Γ → Tm Γ

  abs : Tm (ext Γ) → Tm Γ 


For your homework, implement the function wk-Tm : (Γ : Ctx) → Tm Γ → Tm (ext Γ) that weakens terms to a context with one more variable in scope. In my talk, we’ll see how we can greatly simplify the definition of wk-Tm in the setting of directed type theory! 
