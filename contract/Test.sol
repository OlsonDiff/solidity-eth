// File @openzeppelin/contracts/utils/Context.sol@v4.8.2

// SPDX-License-Identifier: MIT AND UNLICENSED
// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}


// File @openzeppelin/contracts/access/Ownable.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.7.0) (access/Ownable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


// File @openzeppelin/contracts/security/Pausable.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}


// File @openzeppelin/contracts/utils/math/Math.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/Math.sol)

pragma solidity ^0.8.0;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv)
     * with further edits by Uniswap Labs also under MIT license.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1);

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator. Always >= 1.
            // See https://cs.stackexchange.com/q/138556/92363.

            // Does not overflow because the denominator cannot be zero at this stage in the function.
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also works
            // in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator,
        Rounding rounding
    ) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (rounding == Rounding.Up && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10**64) {
                value /= 10**64;
                result += 64;
            }
            if (value >= 10**32) {
                value /= 10**32;
                result += 32;
            }
            if (value >= 10**16) {
                value /= 10**16;
                result += 16;
            }
            if (value >= 10**8) {
                value /= 10**8;
                result += 8;
            }
            if (value >= 10**4) {
                value /= 10**4;
                result += 4;
            }
            if (value >= 10**2) {
                value /= 10**2;
                result += 2;
            }
            if (value >= 10**1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10**result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result * 8) < value ? 1 : 0);
        }
    }
}


// File @openzeppelin/contracts/utils/Strings.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.8.0) (utils/Strings.sol)

pragma solidity ^0.8.0;

/**
 * @dev String operations.
 */
library Strings {
    bytes16 private constant _SYMBOLS = "0123456789abcdef";
    uint8 private constant _ADDRESS_LENGTH = 20;

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = Math.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            /// @solidity memory-safe-assembly
            assembly {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                /// @solidity memory-safe-assembly
                assembly {
                    mstore8(ptr, byte(mod(value, 10), _SYMBOLS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, Math.log256(value) + 1);
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "Strings: hex length insufficient");
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), _ADDRESS_LENGTH);
    }
}


// File @openzeppelin/contracts/security/ReentrancyGuard.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.8.0) (security/ReentrancyGuard.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}


// File @openzeppelin/contracts/utils/math/SafeMath.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.6.0) (utils/math/SafeMath.sol)

pragma solidity ^0.8.0;

// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}


// File contracts/interfaces/IBEP20.sol


pragma solidity ^0.8.17;

interface IBEP20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the token decimals.
     */
    function decimals() external view returns (uint8);

    /**
     * @dev Returns the token symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the token name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the bep token owner.
     */
    function getOwner() external view returns (address);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address _owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


// File @openzeppelin/contracts/utils/Address.sol@v4.8.2


// OpenZeppelin Contracts (last updated v4.8.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}


// File contracts/utils/SafeBEP20.sol



pragma solidity ^0.8.17;



/**
 * @title SafeBEP20
 * @dev Wrappers around BEP20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeBEP20 for IBEP20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeBEP20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IBEP20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IBEP20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IBEP20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IBEP20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeBEP20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IBEP20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IBEP20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeBEP20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IBEP20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeBEP20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeBEP20: BEP20 operation did not succeed");
        }
    }
}


// File contracts/utils/Whitelist.sol


pragma solidity ^0.8.17;


contract Whitelist is Pausable {
    using SafeMath for uint256;

    mapping(address => bool) public whitelist;
    mapping(address => uint256) public userTier;
    mapping(address => uint256) public whitelistIndex;

    string public clientSeed;
    string public serverSeed;
    uint public nonce;

    uint public currentWhitelisted = 0;

    uint public poolStartDate;

    address public poolCreator;

    struct WhitelistItem {
        bool isPublic;
        address walletAddress;
        uint256 tier;
    }

    WhitelistItem[] public whitelistItems;

    event AddedToWhitelist(address accounts, address poolAddress);
    event RandomAddedToWhitelist(
        address accounts,
        uint _tier,
        address poolAddress
    );
    event RemovedFromWhitelist(address _address, address poolAddress);

    modifier onlyWhitelisted() {
        require(isWhitelisted(msg.sender), "only whitelist address can call");
        _;
    }

    modifier onlyPoolCreator() {
        require(
            msg.sender == poolCreator,
            "only Pool Creator address can call"
        );
        _;
    }

    /* ========== CONSTRUCTOR ========== */

    constructor(
        address _address,
        uint256 _startDate,
        string memory _serverSeed
    ) public {
        poolStartDate = _startDate;
        poolCreator = _address;
        serverSeed = _serverSeed;
    }

    modifier beforePoolStart() {
        require(block.timestamp <= poolStartDate);
        _;
    }

    function changeClientSeed(string memory _clientSeed) public {
        clientSeed = _clientSeed;
    }

    // 1 = Tier1
    // 2 = Tier2
    // 3 = tier3
    // 4 = Tier4
    // 5 = Tier5
    // 6 = Gamers
    function addPublicRandom(
        address[] memory _addresses,
        uint256[] calldata _tier,
        uint _maximumWhitelisted,
        string memory _serverSeed
    ) public onlyPoolCreator beforePoolStart {
        require(_addresses.length > 0, " _addresses length is zero");
        uint totalWhitelisted;
        require(_addresses.length >= _maximumWhitelisted, "less address");
        uint arrlength = _addresses.length;
        for (uint i = 0; i < (_maximumWhitelisted.div(32)).add(1); i++) {
            nonce++;
            bytes32 hash = (
                keccak256(abi.encode(_serverSeed, clientSeed, nonce))
            );
            for (uint j = 0; j < 32; j++) {
                if (totalWhitelisted < _maximumWhitelisted) {
                    uint256 val = uint(bytes32(hash[j])).mod(arrlength);
                    whitelist[_addresses[val]] = true;
                    require(_tier[val] > 0 && _tier[val] <= 6, "not a valid tier");
                    userTier[_addresses[val]] = _tier[val];
                    whitelistItems.push(
                        WhitelistItem(
                            true,
                            _addresses[val],
                            _tier[val]
                        )
                    );
                    delete _addresses[arrlength - 1];
                    arrlength = arrlength.sub(1);
                    whitelistIndex[_addresses[val]] = totalWhitelisted;
                    totalWhitelisted = totalWhitelisted.add(1);
                    emit RandomAddedToWhitelist(
                        _addresses[val],
                        _tier[val],
                        address(this)
                    );
                    _addresses[val] = _addresses[arrlength - 1];
                }
            }
        }
        currentWhitelisted = currentWhitelisted.add(totalWhitelisted);
    }

    /* Whitelist Private Users */

    function addPrivate(
        address[] memory _addresses
    ) external onlyPoolCreator beforePoolStart {
        uint totalWhitelisted;
        for (uint i = 0; i < _addresses.length; i++) {
            require(_addresses[i] != address(0), "address must be valid");
            if (whitelist[_addresses[i]] != true) {
                whitelist[_addresses[i]] = true;
                whitelistItems.push(
                    WhitelistItem(
                        false,
                        _addresses[i],
                        6
                    )
                );
                userTier[_addresses[i]] = 6;
                whitelistIndex[_addresses[i]] = totalWhitelisted;
                totalWhitelisted += 1;
                emit AddedToWhitelist(_addresses[i], address(this));
            }
        }
        currentWhitelisted = currentWhitelisted.add(totalWhitelisted);
    }

    function remove(
        address[] memory _addresses,
        uint[] memory _index
    ) external onlyPoolCreator beforePoolStart {
        require(
            _addresses.length <= currentWhitelisted,
            "remove only whitelist address"
        );

        uint totalWhitelisted;
        for (uint i = 0; i < _addresses.length; i++) {
            require(
                whitelistItems[_index[i]].walletAddress == _addresses[i],
                "use valid address"
            );
            whitelist[_addresses[i]] = false;
            whitelistItems[_index[i]] = whitelistItems[
                whitelistItems.length - 1
            ];
            delete whitelistItems[whitelistItems.length - 1];
            totalWhitelisted -= 1;
            emit RemovedFromWhitelist(_addresses[i], address(this));
        }
        currentWhitelisted = currentWhitelisted.sub(totalWhitelisted);
    }

    function isWhitelisted(address _address) public view returns (bool) {
        return whitelist[_address];
    }

    function getUserTier(address _address) public view returns (uint256) {
        if (isWhitelisted(_address)) {
            return userTier[_address];
        } else {
            return 0;
        }
    }

    function pause() public onlyPoolCreator {
        _pause();
    }

    function unpause() public onlyPoolCreator {
        _unpause();
    }

    function getWhitelistedAddresses()
        external
        view
        returns (WhitelistItem[] memory)
    {
        return whitelistItems;
    }
}


// File contracts/Pool.sol


pragma experimental ABIEncoderV2;
pragma solidity ^0.8.17;




contract Pool is Whitelist, ReentrancyGuard {
    using SafeMath for uint256;
    using SafeBEP20 for IBEP20;

    uint256 increment = 0;

    mapping(address => Purchase) public purchases;

    struct Purchase {
        uint256 amount;
        address purchaser;
        uint256 fundAmount;
        uint256 timestamp;
        bool wasFinalized;
        bool reverted;
    }

    IBEP20 public ibep20;
    bool public isSaleFunded = false;
    uint public decimals = 0;
    bool public unsoldTokensReedemed = false;
    uint256 public tradeValue;
    uint256 public endDate;
    uint256[6] public individualMinimumAmount;
    uint256[6] public individualMaximumAmount;

    uint256 public minimumRaise;

    uint256 public tokensAllocated = 0;
    uint256 public tokensForSale = 0;
    bool public poolType; // for standard put false and instant put true
    uint public constant DENOMINATOR = 10000;

    address payable public fundAddress;

    address payable public FEE_ADDRESS;
    uint256 public feePercentage;
    uint256 public feeAmount = 0;
    address public factoryContract;

    uint public publicPurchaseableAmount;
    uint public privatePurchaseableAmount;

    bool public isSetTierLimit;
    bool public isNativeToken;
    IBEP20 public fundToken;

    event PurchaseEvent(
        uint256 amount,
        address indexed purchaser,
        uint256 timestamp,
        address poolAddress
    );
    event RedeemEvent(
        uint256 amount,
        address indexed purchaser,
        address poolAddress
    );
    event AddFund(uint amount, address poolAddress);
    event WithdrawFunds(address indexed _owner, address poolAddress);
    event RedeemGivenMinimumGoalNotAchieved(
        address purchaser,
        address poolAddress
    );
    event SetFundAddress(address _fundAddress);
    event SetFeePercentage(uint256 _feePercentage);

    /* ========== CONSTRUCTOR ========== */

    constructor(
        address _tokenAddress,
        uint256 _tradeValue,
        uint256 _tokensForSale,
        uint256 _startDate,
        uint256 _endDate,
        bool _poolType,
        uint256 _minimumRaise,
        address _address,
        string memory _serverSeed,
        address _factoryContract
    ) public Whitelist(_address, _startDate, _serverSeed) {
        require(
            _tokenAddress != address(0) && _address != address(0),
            "invalid address"
        );
        require(_tradeValue > 0, "Trade value should be over 0");
        require(
            block.timestamp < _endDate,
            "End Date should be further than current date"
        );
        require(
            block.timestamp < _startDate,
            "Start Date should be further than current date"
        );
        require(
            _startDate < _endDate,
            "End Date must be later than Start Date"
        );
        require(_tokensForSale > 0, "Tokens for Sale should be over 0");
        require(
            _minimumRaise <= DENOMINATOR,
            "Minimum Raise Percentage should be less than Denominator"
        );

        tokensForSale = _tokensForSale;
        tradeValue = _tradeValue;
        poolStartDate = _startDate;
        endDate = _endDate;
        poolType = _poolType;
        if (!_poolType) {
            /* If raise is not atomic swap */
            minimumRaise = _tokensForSale.mul(_minimumRaise).div(DENOMINATOR);
        }
        ibep20 = IBEP20(_tokenAddress);
        decimals = ibep20.decimals();
        factoryContract = _factoryContract;
    }

    /* One Time Call Function for Set User Limit */
    function setDistributionRatio(
        uint256 _publicRatio
    ) external beforePoolStart {
        require(msg.sender == factoryContract, "only valid address can call");
        require(
            _publicRatio < DENOMINATOR,
            "_publicRatio must smaller than DENOMINATOR"
        );
        publicPurchaseableAmount = tokensForSale.mul(_publicRatio).div(
            DENOMINATOR
        );
        privatePurchaseableAmount = tokensForSale.sub(publicPurchaseableAmount);
    }

    /* One Time Call Funciton for Set fund token type */
    function setTokenType(
        bool _isNativeToken,
        address _fundTokenAddress
    ) external beforePoolStart {
        require(msg.sender == factoryContract, "only valid address can call");
        isNativeToken = _isNativeToken;
        if (!_isNativeToken) {
            fundToken = IBEP20(_fundTokenAddress);
        }
    }

    /**
     * set individual tier limit .
     */
    function setTierLimit(
        uint256[5] memory _individualMinimumAmount,
        uint256[5] memory _individualMaximumAmount
    ) external beforePoolStart {
        require(msg.sender == poolCreator, "only valid address can call");
        for (uint i; i < 5; i++) {
            require(
                _individualMaximumAmount[i] >= _individualMinimumAmount[i],
                "Individual Maximim AMount should be > Individual Minimum Amount"
            );
            require(
                tokensForSale >= _individualMinimumAmount[i],
                "Tokens for Sale should be > Individual Minimum Amount"
            );
            require(
                tokensForSale >= _individualMaximumAmount[i],
                "Tokens for Sale should be > Individual maximum Amount"
            );
            individualMinimumAmount[i] = _individualMinimumAmount[i];
            individualMaximumAmount[i] = _individualMaximumAmount[i];
        }
        isSetTierLimit = true;
    }

    function setNewOwner(address _address) public {
        require(
            factoryContract == msg.sender,
            "only factory contract can call"
        );
        poolCreator = _address;
    }

    function setFundAddress(
        address payable _fundAddress
    ) public onlyPoolCreator {
        require(_fundAddress != address(0), "Set valid address");
        fundAddress = _fundAddress;
        emit SetFundAddress(_fundAddress);
    }

    function setTreasurerAddress(
        address payable _treasurer
    ) public onlyPoolCreator beforePoolStart {
        FEE_ADDRESS = _treasurer;
    }

    function setFeePercentage(
        uint256 _feePercentage
    ) public onlyPoolCreator beforePoolStart {
        require(
            _feePercentage < DENOMINATOR && _feePercentage > 0,
            "set Valid fee percentage"
        );
        feePercentage = _feePercentage;
        emit SetFeePercentage(_feePercentage);
    }

    /**
     * Modifier to make a function callable only when the contract has Atomic Swaps not available.
     */

    modifier isNotInstant() {
        require(!poolType, "Has to be non instant swap");
        _;
    }

    /**
     * Modifier to make a function callable only when the contract has Atomic Swaps not available.
     */
    modifier isSaleFinalized() {
        require(hasFinalized(), "Has to be finalized");
        _;
    }

    /**
     * Modifier to make a function callable only when the swap time is open.
     */
    modifier isSaleOpen() {
        require(isOpen(), "Has to be open");
        _;
    }

    /**
     * Modifier to make a function callable only when the contract has Atomic Swaps not available.
     */

    modifier isFunded() {
        require(isSaleFunded, "Has to be funded");
        _;
    }

    /* ========== VIEWS ========== */

    function getStartDate() public view returns (uint) {
        return poolStartDate;
    }

    /* Get Functions */
    function totalRaiseCost() public view returns (uint256) {
        return (cost(tokensForSale));
    }

    function availableTokens() public view returns (uint256) {
        return ibep20.balanceOf(address(this));
    }

    function tokensLeft() public view returns (uint256) {
        return tokensForSale - tokensAllocated;
    }

    function hasMinimumRaise() public view returns (bool) {
        return (minimumRaise != 0);
    }

    /* Verify if minimum raise was not achieved */
    function minimumRaiseNotAchieved() public view returns (bool) {
        require(
            cost(tokensAllocated) < cost(minimumRaise),
            "TotalRaise is bigger than minimum raise amount"
        );
        return true;
    }

    /* Verify if minimum raise was achieved */
    function minimumRaiseAchieved() public view returns (bool) {
        if (hasMinimumRaise()) {
            require(
                cost(tokensAllocated) >= cost(minimumRaise),
                "TotalRaise is less than minimum raise amount"
            );
        }
        return true;
    }

    function hasFinalized() public view returns (bool) {
        return block.timestamp > endDate;
    }

    function hasStarted() public view returns (bool) {
        return block.timestamp >= poolStartDate;
    }

    function isOpen() public view returns (bool) {
        return hasStarted() && !hasFinalized();
    }

    function cost(uint256 _amount) public view returns (uint) {
        return _amount.mul(tradeValue).div(10 ** decimals);
    }

    function costFee(uint _amount) public view returns (uint) {
        uint fee = _amount
            .mul(tradeValue)
            .div(10 ** decimals)
            .mul(feePercentage)
            .div(DENOMINATOR);
        return fee;
    }

    function getPurchase(
        address wallet
    ) external view returns (uint256, address, uint256, uint256, bool, bool) {
        Purchase memory purchase = purchases[wallet];
        return (
            purchase.amount,
            purchase.purchaser,
            purchase.fundAmount,
            purchase.timestamp,
            purchase.wasFinalized,
            purchase.reverted
        );
    }

    /* Add Tokens for Sale */

    function addTokensForSale(uint256 _amount) public beforePoolStart {
        require(
            ibep20.balanceOf(msg.sender) >= _amount,
            "token balance is low"
        );
        require(
            _amount >= tokensForSale,
            "Transfered tokens have to be equal or less than proposed"
        );
        ibep20.safeTransferFrom(msg.sender, address(this), _amount);
        isSaleFunded = true;
        emit AddFund(_amount, address(this));
    }

    /* For Token Exchange */

    function swap(
        uint256 _amount
    ) external payable whenNotPaused isFunded isSaleOpen onlyWhitelisted {
        require(_amount > 0, "Amount has to be positive");
        require(
            _amount <= tokensLeft(),
            "Amount is less than tokens available"
        );
        uint256 totalCost = cost(_amount).add(costFee(_amount));
        if (isNativeToken) {
            require(
                msg.value == totalCost,
                "User has to cover the cost of the swap in BNB, use the cost function to determine"
            );
        }
        uint256 tier = getUserTier(msg.sender);
        require(tier >= 0, "Only valid users can swap this tokens");

        Purchase memory currentPurchase = purchases[msg.sender];
        uint256 purchaserTotalAmountPurchased = currentPurchase.amount;
        if (tier != 6) {
            if (isSetTierLimit) {
                require(
                    purchaserTotalAmountPurchased.add(_amount) >=
                        individualMinimumAmount[tier - 1],
                    "Amount is less than minimum amount"
                );
                require(
                    purchaserTotalAmountPurchased.add(_amount) <=
                        individualMaximumAmount[tier - 1],
                    "Address has already passed the max amount of swap"
                );
            } else {
                require(
                    purchaserTotalAmountPurchased.add(_amount) <= tokensForSale,
                    "Address has already passed the max amount of swap"
                );
            }
            require(
                publicPurchaseableAmount >= _amount,
                "not sufficient amount available for public sale"
            );
            publicPurchaseableAmount = publicPurchaseableAmount.sub(_amount);
        } else {
            require(
                privatePurchaseableAmount >= _amount,
                "not sufficient amount available for private sale"
            );
            privatePurchaseableAmount = privatePurchaseableAmount.sub(_amount);
        }
        if (poolType) {
            ibep20.safeTransfer(address(msg.sender), _amount);
            currentPurchase.wasFinalized = true;
        }
        if (!isNativeToken) {
            fundToken.safeTransferFrom(address(msg.sender), address(this), totalCost);
        }
        feeAmount = feeAmount.add(costFee(_amount));
        currentPurchase.purchaser = msg.sender;
        currentPurchase.timestamp = block.timestamp;
        currentPurchase.amount = currentPurchase.amount + _amount;
        currentPurchase.fundAmount = currentPurchase.fundAmount + totalCost;
        purchases[msg.sender] = currentPurchase;
        tokensAllocated = tokensAllocated.add(_amount);
        emit PurchaseEvent(_amount, msg.sender, block.timestamp, address(this));
    }

    /* Redeem tokens when the sale was finalized */

    function redeemTokens()
        external
        isNotInstant
        isSaleFinalized
        isFunded
        whenNotPaused
        nonReentrant
    {
        require(
            (purchases[msg.sender].amount != 0) &&
                !purchases[msg.sender].wasFinalized,
            "Purchase is either 0 or finalized"
        );
        require(minimumRaiseAchieved(), "minimun raise has not be reached");
        require(purchases[msg.sender].purchaser == msg.sender, "sender should purchase during ipo");

        purchases[msg.sender].wasFinalized = true;
        ibep20.safeTransfer(msg.sender, purchases[msg.sender].amount);
        emit RedeemEvent(
            purchases[msg.sender].amount,
            msg.sender,
            address(this)
        );
    }

    /* Retrieve Minumum Amount */

    function redeemGivenMinimumGoalNotAchieved()
        external
        isSaleFinalized
        isNotInstant
        nonReentrant
    {
        require(hasMinimumRaise(), "Minimum raise has to exist");
        require(minimumRaiseNotAchieved(), "Minimum raise has to be reached");
        /* Confirm it exists and was not finalized */
        require(
            (purchases[msg.sender].amount != 0) &&
                !purchases[msg.sender].wasFinalized,
            "Purchase is either 0 or finalized"
        );

        require(purchases[msg.sender].purchaser == msg.sender);
        purchases[msg.sender].wasFinalized = true;
        purchases[msg.sender].reverted = true;
        if (isNativeToken) {
            payable(msg.sender).transfer(purchases[msg.sender].fundAmount);
        } else {
            fundToken.safeTransfer(msg.sender, purchases[msg.sender].fundAmount);
        }
        emit RedeemGivenMinimumGoalNotAchieved(msg.sender, address(this));
    }

    /* Admin Functions for Withdrow sale Funds */

    function withdrawFunds()
        external
        whenNotPaused
        onlyPoolCreator
        isSaleFinalized
    {
        require(minimumRaiseAchieved(), "Minimum raise has to be reached");
        if (isNativeToken) {
            FEE_ADDRESS.transfer(feeAmount); /* Fee Address */
            fundAddress.transfer(address(this).balance);
        } else {
            fundToken.safeTransfer(FEE_ADDRESS, feeAmount);
            fundToken.safeTransfer(fundAddress, fundToken.balanceOf(address(this)));
        }
        emit WithdrawFunds(msg.sender, address(this));
    }

    /* Admin Functions for Withdrow Unsold Tokens  */

    function withdrawUnsoldTokens() external onlyPoolCreator isSaleFinalized {
        require(!unsoldTokensReedemed);
        uint256 unsoldTokens;
        if (hasMinimumRaise() && (cost(tokensAllocated) < cost(minimumRaise))) {
            unsoldTokens = tokensForSale;
        } else {
            unsoldTokens = tokensForSale.sub(tokensAllocated);
        }
        if (unsoldTokens > 0) {
            unsoldTokensReedemed = true;
            ibep20.safeTransfer(fundAddress, unsoldTokens);
        }
    }

    function removeOtherBEP20Tokens(
        address _tokenAddress,
        address _to
    ) external onlyPoolCreator isSaleFinalized {
        require(
            _tokenAddress != address(ibep20),
            "Token Address has to be diff than the ibep20 subject to sale"
        );
        IBEP20 ibep20Token = IBEP20(_tokenAddress);
        ibep20Token.safeTransfer(_to, ibep20Token.balanceOf(address(this)));
    }
}


// File contracts/utils/Authorizable.sol


pragma solidity ^0.8.17;


contract Authorizable is Ownable {
    using SafeMath for uint256;

    mapping(address => bool) public authorized;

    event AddAuthorized(address indexed _address);
    event RemoveAuthorized(address indexed _address);

    modifier onlyAuthorized() {
        require(
            authorized[msg.sender] || owner() == msg.sender,
            "Card Authorizable: caller is not the SuperAdmin or Admin"
        );
        _;
    }

    function addAuthorized(address _toAdd) external onlyOwner {
        require(
            _toAdd != address(0),
            "Card Authorizable: _toAdd isn't vaild address"
        );
        require(
            !authorized[_toAdd],
            "Card Authorizable: _toAdd is already added"
        );
        authorized[_toAdd] = true;
        emit AddAuthorized(_toAdd);
    }

    function removeAuthorized(address _toRemove) external onlyOwner {
        require(
            _toRemove != address(0),
            "Card Authorizable: _toRemove isn't vaild address"
        );
        require(
            authorized[_toRemove],
            "Card Authorizable: _toRemove is not authorized"
        );
        authorized[_toRemove] = false;
        emit RemoveAuthorized(_toRemove);
    }
}


// File contracts/PoolFactory.sol


pragma solidity ^0.8.17;



contract PoolFactory is Authorizable {
    using SafeMath for uint256;

    mapping(address => bool) private _isPool;

    address[] public poolAddress;

    uint256 public timeGap;
    uint256 public poolDuration;

    address[] public fundTokens;

    /* ========== EVENTS ========== */

    event PoolCreated(
        string _name,
        address poolAddress,
        address poolOwner,
        address indexed _tokenAddress,
        uint256 _tradeValue,
        uint256 _tokensForSale,
        bool _poolType,
        uint256 _minimumRaise,
        string _serverSeed,
        uint256[2] _date
    );
    event SetDistributionRatio(address poolAddress, uint _publicRatio);
    event SetFundTokenType(address poolAddress, uint _tokenType);
    event TransferOwnership(address poolAddress, address newOwner);

    /* ========== CONSTRUCTOR ========== */

    constructor(
        address[] memory stableCoins
    ) public {
        timeGap = 600;
        poolDuration = 600;
        fundTokens = stableCoins;
    }

    /* ========== CREATION OF NEW POOL ========== */

    function newPool(
        string memory _name,
        address _tokenAddress,
        uint256 _tradeValue,
        uint256 _tokensForSale,
        uint[2] memory _date,
        uint _publicRatio,
        bool _poolType,
        uint256 _minimumRaise,
        uint _tokenType
    ) external onlyAuthorized {
        require(
            _date[0] >= timeGap.add(block.timestamp),
            "Start Date should be further than current date + time gap"
        );
        require(
            _date[1] >= _date[0].add(poolDuration),
            "End date must be greater than min duration time + start time"
        );
        Pool pool = new Pool(
            _tokenAddress,
            _tradeValue,
            _tokensForSale,
            _date[0],
            _date[1],
            _poolType,
            _minimumRaise,
            msg.sender,
            Strings.toHexString(uint256(uint160(msg.sender)), 20),
            address(this)
        );
        emit PoolCreated(
            _name,
            address(pool),
            msg.sender,
            _tokenAddress,
            _tradeValue,
            _tokensForSale,
            _poolType,
            _minimumRaise,
            Strings.toHexString(uint256(uint160(msg.sender)), 20),
            _date
        );
        pool.setDistributionRatio(_publicRatio);
        emit SetDistributionRatio(address(pool), _publicRatio);
        if (_tokenType == 0) {
            pool.setTokenType(true, address(0));
        } else {
            pool.setTokenType(false, fundTokens[_tokenType - 1]);
        }
        emit SetFundTokenType(address(pool), _tokenType);
        _isPool[address(pool)] = true;
        poolAddress.push(address(pool));
    }

    function changeTimeGap(uint256 _timeInSec) public onlyAuthorized {
        timeGap = _timeInSec;
    }

    function updateMinPoolDuration(
        uint256 _poolDuration
    ) public onlyAuthorized {
        poolDuration = _poolDuration;
    }

    function transferOwnership(address _poolAddress, address newOwner) public {
        Pool pool = Pool(_poolAddress);
        require(newOwner != address(0), "new owner is the zero address");
        require(msg.sender == pool.poolCreator(), "only pool creator can call");
        pool.setNewOwner(newOwner);
        emit TransferOwnership(_poolAddress, newOwner);
    }

    function addNewStableCoin(
        address tokenAddress
    ) public onlyOwner {
        fundTokens.push(tokenAddress);
    }
}