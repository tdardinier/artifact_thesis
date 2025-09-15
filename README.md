# Isabelle Theories for *Formal Foundations for Automated Deductive Verifiers* (2025)

This repository contains [Isabelle](https://isabelle.in.tum.de/) theories that support all formal claims from the PhD thesis *Formal Foundations for Automated Deductive Verifiers* (Thibault Dardinier, 2025).
All `.thy` files have been successfully checked with Isabelle 2025.

## Overview of formal results by chapter
- **Chapter 2**: `Chapter2_TranslationalVerifiers.thy`  
- **Chapter 3**: `Chapter3_FractionalPredicates.thy`  
- **Chapter 4**: `Chapter4_Wands.thy`  
- **Chapter 5**: `Chapters56_HHL_Hypra.thy`  
- **Chapter 6**: `Chapters56_HHL_Hypra.thy`  

To explore the results of a specific chapter, open the corresponding file in the Isabelle IDE.

## Structure of the formalization
The development is organized into eight main folders:  
- **CoreIVL**: Formalizes the IDF algebra and CoreIVL (Chapter 2)  
- **Fractions**: Formalizes results on fractional predicates (Chapter 3)  
- **FrontEnd**: Formalizes the simple parallel front-end and its soundness proof (Chapter 2)  
- **HyperHoareLogic**: Formalizes Hyper Hoare Logic and results for Hypra (Chapters 5 and 6)  
- **SymEx**: Formalizes a symbolic execution engine for Viper and proves its soundness against CoreIVL (Chapter 2)  
- **VCG**: Formalizes the semantics of Viper’s verification condition generator and proves its soundness against CoreIVL (Chapter 2)  
- **Viper**: Formalizes the Viper intermediate verification language, and instantiates CoreIVL with it (Chapter 2)  
- **Wands**: Formalizes results about the package logic and combinable wands (Chapter 4)  

## Relation to prior artifacts
Earlier versions of many files in this artifact were published as parts of the following paper artifacts:  

- *Sound Automation of Magic Wands*,  
  Thibault Dardinier, Gaurav Parthasarathy, Noé Weeks, Peter Müller, Alexander J. Summers
  CAV 2022

- *Fractional Resources in Unbounded Separation Logic*,  
  Thibault Dardinier, Peter Müller, Alexander J. Summers
  OOPSLA 2022

- *Towards Trustworthy Automated Program Verifiers: Formally Validating Translations into an Intermediate Verification Language*,  
  Gaurav Parthasarathy, Thibault Dardinier, Benjamin Bonneau, Peter Müller, Alexander J. Summers
  PLDI 2024

- *Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties*,  
  Thibault Dardinier, Peter Müller
  PLDI 2024

- *Hypra: A Deductive Program Verifier for Hyper Hoare Logic*,  
  Thibault Dardinier, Anqi Li, Peter Müller
  OOPSLA 2024

- *Formal Foundations for Translational Separation Logic Verifiers*,  
  Thibault Dardinier, Michael Sammler, Gaurav Parthasarathy, Alexander J. Summers, Peter Müller
  POPL 2025

In particular, Gaurav Parthasarathy is the main author of the files in the `VCG` folder, and contributed significantly to files in the `Viper` folder.
Michael Sammler is the main author of the files in the `SymEx` folder, of the VCG soundness proof (`VCG/AbstractRefinesTotal.thy`), and contributed to files in the `CoreIVL` folder.
Finally, the files `FrontEnd/VHelper.thy` and `FrontEnd/ParImp.thy` have been adapted from work by Qin Yu and James Brotherston (for Isabelle 2016-1).
