// Simplified Yul representation of ERC20 transfer function
// This demonstrates key patterns that would appear in real contracts

object "SimpleERC20" {
    code {
        // Constructor - sets initial supply
        function constructor_SimpleERC20(initialSupply) {
            let sender := caller()
            sstore(0x0, initialSupply) // totalSupply at slot 0

            // balanceOf[msg.sender] = initialSupply
            let balanceSlot := keccak256(sender, 0x1)
            sstore(balanceSlot, initialSupply)
        }

        // Transfer function: balanceOf[from] -= value; balanceOf[to] += value
        function transfer(to, value) -> success {
            let sender := caller()

            // Check sender balance
            let senderBalanceSlot := keccak256(sender, 0x1)
            let senderBalance := sload(senderBalanceSlot)

            // Require: sender has enough balance
            if lt(senderBalance, value) {
                invalid() // revert
            }

            // Require: recipient is not zero address
            if iszero(to) {
                invalid()
            }

            // Subtract from sender
            let newSenderBalance := sub(senderBalance, value)
            sstore(senderBalanceSlot, newSenderBalance)

            // Add to recipient
            let toBalanceSlot := keccak256(to, 0x1)
            let toBalance := sload(toBalanceSlot)
            let newToBalance := add(toBalance, value)
            sstore(toBalanceSlot, newToBalance)

            // Assertion: conservation of tokens
            // In a full implementation, we'd check that sender + recipient balance change = 0
            if iszero(gt(newSenderBalance, sub(senderBalance, value))) {
                // This should never happen with correct arithmetic
                invalid()
            }

            success := 1
        }

        // Balance query
        function balanceOf(account) -> balance {
            let balanceSlot := keccak256(account, 0x1)
            balance := sload(balanceSlot)
        }

        // Total supply query
        function totalSupply() -> supply {
            supply := sload(0x0)
        }
    }
}
