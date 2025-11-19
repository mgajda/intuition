// Reentrancy Guard pattern
// Demonstrates state machine verification

object "ReentrancyGuard" {
    code {
        function nonReentrant(status) -> new_status {
            // Assert not already entered (status should be 0)
            if iszero(iszero(status)) {
                invalid()
            }

            // Set status to 1 (entered)
            new_status := 1
        }

        function exitNonReentrant(status) -> new_status {
            // Assert we are in entered state (status should be 1)
            if iszero(eq(status, 1)) {
                invalid()
            }

            // Reset status to 0
            new_status := 0
        }

        // Test: enter and exit
        let initial_status := 0

        // Enter
        let entered_status := nonReentrant(initial_status)
        if iszero(eq(entered_status, 1)) {
            invalid()
        }

        // Exit
        let final_status := exitNonReentrant(entered_status)
        if iszero(eq(final_status, 0)) {
            invalid()
        }

        // Try to re-enter (should fail) - this is commented out for valid code
        // nonReentrant(entered_status)  // Would trigger invalid()
    }
}
