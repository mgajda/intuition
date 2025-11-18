// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SimpleAuction {
    address public beneficiary;
    uint public auctionEnd;
    address public highestBidder;
    uint public highestBid;
    bool public ended;

    mapping(address => uint) public pendingReturns;

    event HighestBidIncreased(address bidder, uint amount);
    event AuctionEnded(address winner, uint amount);

    constructor(uint _biddingTime, address _beneficiary) {
        beneficiary = _beneficiary;
        auctionEnd = block.timestamp + _biddingTime;
    }

    function bid() public payable {
        require(block.timestamp <= auctionEnd, "Auction ended");
        require(msg.value > highestBid, "Bid too low");

        if (highestBid != 0) {
            pendingReturns[highestBidder] += highestBid;
        }

        highestBidder = msg.sender;
        highestBid = msg.value;

        emit HighestBidIncreased(msg.sender, msg.value);
    }

    function withdraw() public returns (bool) {
        uint amount = pendingReturns[msg.sender];
        if (amount > 0) {
            pendingReturns[msg.sender] = 0;
            assert(pendingReturns[msg.sender] == 0);

            if (!payable(msg.sender).send(amount)) {
                pendingReturns[msg.sender] = amount;
                return false;
            }
        }
        return true;
    }
}
