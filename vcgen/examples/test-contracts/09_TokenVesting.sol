// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract TokenVesting {
    address public beneficiary;
    uint public start;
    uint public cliff;
    uint public duration;
    uint public released;

    constructor(address _beneficiary, uint _start, uint _cliff, uint _duration) {
        require(_beneficiary != address(0), "Invalid beneficiary");
        require(_cliff <= _duration, "Cliff exceeds duration");

        beneficiary = _beneficiary;
        start = _start;
        cliff = _cliff;
        duration = _duration;
        released = 0;
    }

    function vestedAmount(uint total) public view returns (uint) {
        if (block.timestamp < start + cliff) {
            return 0;
        } else if (block.timestamp >= start + duration) {
            return total;
        } else {
            uint vested = (total * (block.timestamp - start)) / duration;
            assert(vested <= total);
            return vested;
        }
    }
}
