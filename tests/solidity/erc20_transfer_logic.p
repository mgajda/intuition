% ERC20 transfer logic (propositional abstraction)
%
% Abstract the transfer function logic:
% - has_balance: sender has sufficient balance
% - valid_recipient: recipient is not zero address
% - transfer_success: transfer succeeds
%
% Property: If sender has balance AND recipient is valid, then transfer succeeds

fof(erc20_transfer_preconditions, conjecture,
    ((has_balance & valid_recipient) => transfer_success)).
