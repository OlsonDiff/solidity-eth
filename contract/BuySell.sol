// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract USDCExchange is Ownable {
    IERC20 public usdcToken;
    uint256 public buyPrice; // Price of 1 USDC in wei
    uint256 public sellPrice; // Price of 1 USDC in wei

    event BuyUSDC(address indexed buyer, uint256 amount);
    event SellUSDC(address indexed seller, uint256 amount);

    constructor(address _usdcTokenAddress, uint256 _buyPrice, uint256 _sellPrice) {
        usdcToken = IERC20(_usdcTokenAddress);
        setPrices(_buyPrice, _sellPrice);
    }

    function setPrices(uint256 _buyPrice, uint256 _sellPrice) public onlyOwner {
        buyPrice = _buyPrice;
        sellPrice = _sellPrice;
    }

    function buyUSDC() public payable {
        require(msg.value > 0, "Send ETH to buy USDC");

        uint256 amountToBuy = msg.value / buyPrice;
        uint256 usdcBalance = usdcToken.balanceOf(address(this));
        
        require(amountToBuy <= usdcBalance, "Not enough USDC in contract");

        usdcToken.transfer(msg.sender, amountToBuy);
        emit BuyUSDC(msg.sender, amountToBuy);
    }

    function sellUSDC(uint256 _amount) public {
        require(_amount > 0, "Specify an amount of USDC to sell");

        uint256 ethAmount = _amount * sellPrice;
        uint256 contractEthBalance = address(this).balance;

        require(ethAmount <= contractEthBalance, "Not enough ETH in contract");

        usdcToken.transferFrom(msg.sender, address(this), _amount);
        payable(msg.sender).transfer(ethAmount);
        emit SellUSDC(msg.sender, _amount);
    }

    function withdrawETH(uint256 _amount) public onlyOwner {
        require(_amount <= address(this).balance, "Not enough ETH in contract");
        payable(owner()).transfer(_amount);
    }

    function withdrawUSDC(uint256 _amount) public onlyOwner {
        require(_amount <= usdcToken.balanceOf(address(this)), "Not enough USDC in contract");
        usdcToken.transfer(owner(), _amount);
    }

    receive() external payable {}
}
