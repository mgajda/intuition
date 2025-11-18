% Escrow: if released once, cannot release again
% released => (try_release => already_released)
% Or: released => ~can_release

fof(escrow_no_double_release, conjecture,
    (released => ~ can_release)).
