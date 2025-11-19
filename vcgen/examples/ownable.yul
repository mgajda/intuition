// Ownable pattern - access control
// Demonstrates authorization checks

object "Ownable" {
    code {
        function requireOwner(caller, owner) {
            // Only owner can proceed
            if iszero(eq(caller, owner)) {
                invalid()
            }
        }

        function transferOwnership(caller, current_owner, new_owner) -> updated_owner {
            // Require caller is current owner
            requireOwner(caller, current_owner)

            // Require new owner is not zero address
            if iszero(new_owner) {
                invalid()
            }

            updated_owner := new_owner
        }

        // Test scenario
        let owner := 0x1000
        let caller := 0x1000  // Same as owner
        let newOwner := 0x2000

        let finalOwner := transferOwnership(caller, owner, newOwner)

        // Assert ownership transferred
        if iszero(eq(finalOwner, 0x2000)) {
            invalid()
        }
    }
}
