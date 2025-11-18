// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// @title Counter - Simple counter contract for testing
/// @notice This contract demonstrates basic assertions for verification
contract Counter {
    uint256 public count;

    /// @notice Increment the counter
    /// @dev Asserts that new count is greater than old count
    function increment() public {
        uint256 oldCount = count;
        count = count + 1;

        // Assertion: count increased
        assert(count > oldCount);
    }

    /// @notice Decrement the counter
    /// @dev Asserts that count doesn't underflow
    function decrement() public {
        require(count > 0, "Counter: underflow");
        uint256 oldCount = count;
        count = count - 1;

        // Assertion: count decreased
        assert(count < oldCount);
    }

    /// @notice Add a value to the counter
    /// @param value The value to add
    function add(uint256 value) public {
        require(value > 0, "Counter: value must be positive");
        uint256 oldCount = count;
        count = count + value;

        // Assertion: count increased by at least value
        assert(count >= oldCount + value);
    }

    /// @notice Reset counter to zero
    function reset() public {
        count = 0;

        // Assertion: count is zero
        assert(count == 0);
    }
}
