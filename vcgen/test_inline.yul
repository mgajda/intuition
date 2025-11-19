// Test function inlining
object "InlineTest" {
    code {
        function addOne(x) -> result {
            result := add(x, 1)
        }

        let value := 42
        let newValue := addOne(value)

        // Should inline to: gt(add(42, 1), 42) = gt(43, 42) = TRUE
        if iszero(gt(newValue, 42)) {
            invalid()
        }
    }
}
