// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SimpleDEX {
    mapping(address => uint) public ethBalance;
    mapping(address => uint) public tokenBalance;
    uint public rate = 100; // 1 ETH = 100 tokens

    function buyTokens() public payable {
        require(msg.value > 0, "Send ETH");
        uint tokens = msg.value * rate;

        ethBalance[address(this)] += msg.value;
        tokenBalance[msg.sender] += tokens;

        assert(tokenBalance[msg.sender] >= tokens);
    }

    function sellTokens(uint amount) public {
        require(tokenBalance[msg.sender] >= amount, "Insufficient tokens");

        uint eth = amount / rate;
        require(address(this).balance >= eth, "Insufficient ETH");

        tokenBalance[msg.sender] -= amount;
        ethBalance[msg.sender] += eth;

        payable(msg.sender).transfer(eth);

        assert(tokenBalance[msg.sender] + amount >= amount);
    }
}
