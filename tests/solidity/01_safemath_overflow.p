% SafeMath addition overflow check
% Assertion: c >= a where c = a + b
% This should hold for non-negative integers without overflow

fof(safemath_add_no_overflow, conjecture,
    (![A, B, C]: ((C = A + B) => (C >= A)))).
