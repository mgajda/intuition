% Simpler test: ~~(p | ~p) where | is encoded as implications
% (p | ~p) can be encoded as ~~p => p in classical logic
% But for intuitionistic, we test: ~~(~~p => p)
fof(test_dne_stability, conjecture,
    ~ ~ ((~ ~ p) => p)).
