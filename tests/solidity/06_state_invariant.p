% If state S1 implies state S2, and S2 implies S3, then S1 implies S3
% Transitivity of implications

fof(state_transitivity, conjecture,
    (((s1 => s2) & (s2 => s3)) => (s1 => s3))).
