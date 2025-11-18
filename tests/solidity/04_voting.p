% Voting: if already voted, then cannot vote again
% voted => ~can_vote

fof(voting_no_double_vote, conjecture,
    (already_voted => ~ can_vote)).
