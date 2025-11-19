% Verification Condition with Theory Axioms
% Location: if-guard

% Theory Axioms:
fof(transitivity_gt, axiom, ![X,Y,Z]: ((gt(X,Y) & gt(Y,Z)) => gt(X,Z))). % Transitivity: if X > Y and Y > Z then X > Z
fof(asymmetry_gt, axiom, ![X,Y]: (gt(X,Y) => ~gt(Y,X))). % Asymmetry: if X > Y then not Y > X
fof(trichotomy, axiom, ![X,Y]: (gt(X,Y) | eq(X,Y) | gt(Y,X))). % Trichotomy: for any X,Y exactly one holds: X>Y, X=Y, or Y>X
fof(eq_reflexive, axiom, ![X]: eq(X,X)). % Reflexivity: X = X
fof(eq_symmetric, axiom, ![X,Y]: (eq(X,Y) => eq(Y,X))). % Symmetry: if X = Y then Y = X
fof(eq_transitive, axiom, ![X,Y,Z]: ((eq(X,Y) & eq(Y,Z)) => eq(X,Z))). % Transitivity of equality
fof(double_negation, axiom, ![P]: (iszero(iszero(P)) <=> P)). % Double negation elimination
fof(demorgan_and, axiom, ![P,Q]: (iszero(and(P,Q)) <=> (iszero(P) | iszero(Q)))). % De Morgan's law for AND
fof(demorgan_or, axiom, ![P,Q]: (iszero(or(P,Q)) <=> (iszero(P) & iszero(Q)))). % De Morgan's law for OR

% Verification Condition:
fof(vc, conjecture, ~(iszero(gt(newValue, 42)))).
