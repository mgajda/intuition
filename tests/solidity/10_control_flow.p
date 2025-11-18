% If condition C leads to action A, and A leads to state S,
% then condition C leads to state S
% (C => A) => ((A => S) => (C => S))

fof(control_flow_composition, conjecture,
    ((c => a) => ((a => s) => (c => s)))).
