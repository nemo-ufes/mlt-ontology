# Formal Specifications of the MLT Multi-Level Theory

This project includes formal specifications of the Multi-Level Theory (MLT) and its generalization MLT*.

There are two specifications of MLT in order to support the validation and verification of the theory using the Alloy Analyzer (used in [1]):

* [mlt.als](mlt.als) - The first specification of MLT, which assumes static classification
* [mlt_dynamicclassification.als](mlt_dynamicclassification.als) - A minor extension of MLT, indexing the primitive "instance of" predicate with a world variable w, thereby including support for dynamic classification in MLT.

There is also a specification of MLT* in Alloy comprising the following files (used in [2]):

* [mlt_star.als](mlt_star.als) - The specification of MLT* containing all of its definitions;
* [mlt_star_validation.als](mlt_star_validation.als) - The validation of MLT*, containg a series of simulations and constraints that arise from its definitions;
* [mlt_theme_clean1.thm](mlt_theme_clean1.thm) - A basic theme for instance visualization;
* [mlt_theme_clean2.thm](mlt_theme_clean2.thm) - A cleaner theme for instance visualization.

For further information see:
1. Carvalho, V. A., Almeida, J. P. A.: Toward a well-founded theory for multi-level conceptual modeling. Software & Systems Modeling, Springer Berlin Heidelberg, 2016. https://doi.org/10.1007/s10270-016-0538-9
2. Almeida, J. P. A., Fonseca, C. M., Carvalho, V. A., A Comprehensive Formal Theory for Multi-level Conceptual Modeling. In: 36th International Conference on Conceptual Modeling (ER 2017), 2017. https://doi.org/10.1007/978-3-319-69904-2_2

Authors:
* João Paulo A. Almeida;
* Claudenir M. Fonseca;
* Victorio A. Carvalho;

