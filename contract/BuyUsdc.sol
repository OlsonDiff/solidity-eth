// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract BuyUSDC {
    IERC20 public usdcToken;
    address public owner;
    uint256 public rate; // Exchange rate for Ether to USDC

    event TokensPurchased(address indexed buyer, uint256 amountOfETH, uint256 amountOfUSDC);

    constructor(address _usdcTokenAddress, uint256 _rate) {
        require(_usdcTokenAddress != address(0), "Invalid token address");
        require(_rate > 0, "Rate must be greater than 0");

        usdcToken = IERC20(_usdcTokenAddress);
        owner = msg.sender;
        rate = _rate;
    }

    modifier onlyOwner() {
        require(msg.sender == owner, "Only owner can call this function");
        _;
    }

    function buyUSDC() public payable {
        uint256 usdcAmount = msg.value * rate;
        require(usdcToken.balanceOf(address(this)) >= usdcAmount, "Insufficient USDC in contract");

        usdcToken.transfer(msg.sender, usdcAmount);

        emit TokensPurchased(msg.sender, msg.value, usdcAmount);
    }

    function setRate(uint256 _rate) public onlyOwner {
        require(_rate > 0, "Rate must be greater than 0");
        rate = _rate;
    }

    function withdrawETH() public onlyOwner {
        payable(owner).transfer(address(this).balance);
    }

    function withdrawUSDC() public onlyOwner {
        uint256 usdcBalance = usdcToken.balanceOf(address(this));
        usdcToken.transfer(owner, usdcBalance);
    }

    receive() external payable {
        buyUSDC();
    }
}
