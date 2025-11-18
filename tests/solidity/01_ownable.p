% Ownable access control
% If (caller is owner) then (action is authorized)
% Contrapositive: if action requires authorization, caller must be owner

fof(ownable_auth, conjecture,
    (is_owner => authorized)).
