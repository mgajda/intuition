// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Pausable {
    bool private _paused;
    address public owner;

    event Paused(address account);
    event Unpaused(address account);

    constructor() {
        owner = msg.sender;
        _paused = false;
    }

    modifier whenNotPaused() {
        assert(!_paused);
        _;
    }

    modifier whenPaused() {
        assert(_paused);
        _;
    }

    function pause() public {
        require(msg.sender == owner, "Not owner");
        require(!_paused, "Already paused");
        _paused = true;
        emit Paused(msg.sender);
    }

    function unpause() public {
        require(msg.sender == owner, "Not owner");
        require(_paused, "Not paused");
        _paused = false;
        emit Unpaused(msg.sender);
    }
}
