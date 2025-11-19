// ERC20 Transfer pattern with SafeMath checks
// This demonstrates balance checking and overflow prevention

object "ERC20Transfer" {
    code {
        function safeAdd(a, b) -> result {
            result := add(a, b)
            // Assert no overflow: result >= a
            if iszero(or(gt(result, a), eq(result, a))) {
                invalid()
            }
        }

        function safeSub(a, b) -> result {
            // Assert no underflow: a >= b
            if iszero(or(gt(a, b), eq(a, b))) {
                invalid()
            }
            result := sub(a, b)
        }

        // Transfer tokens from sender to recipient
        function transfer(sender_balance, recipient_balance, amount) -> new_sender, new_recipient {
            // Check sender has enough balance
            if iszero(or(gt(sender_balance, amount), eq(sender_balance, amount))) {
                invalid()
            }

            // Use safe math operations
            new_sender := safeSub(sender_balance, amount)
            new_recipient := safeAdd(recipient_balance, amount)

            // Invariant: total supply unchanged
            // sender_balance + recipient_balance == new_sender + new_recipient
            let old_total := add(sender_balance, recipient_balance)
            let new_total := add(new_sender, new_recipient)
            if iszero(eq(old_total, new_total)) {
                invalid()
            }
        }

        // Test: transfer 100 tokens
        let sender := 200
        let recipient := 50
        let amount := 100

        let s, r := transfer(sender, recipient, amount)

        // Assert final balances are correct
        if iszero(eq(s, 100)) {
            invalid()
        }
        if iszero(eq(r, 150)) {
            invalid()
        }
    }
}
