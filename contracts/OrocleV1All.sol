// Sources flattened with hardhat v2.19.4 https://hardhat.org

// SPDX-License-Identifier: Apache-2.0 AND MIT

// File @openzeppelin/contracts/utils/Context.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.4) (utils/Context.sol)

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

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}


// File @openzeppelin/contracts/access/Ownable.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (access/Ownable.sol)

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
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
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


// File @openzeppelin/contracts/utils/math/Math.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (utils/math/Math.sol)

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
    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
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
                // Solidity will revert if denominator == 0, unlike the div opcode on its own.
                // The surrounding unchecked block does not change this fact.
                // See https://docs.soliditylang.org/en/latest/control-structures.html#checked-or-unchecked-arithmetic.
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1, "Math: mulDiv overflow");

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
    function mulDiv(uint256 x, uint256 y, uint256 denominator, Rounding rounding) internal pure returns (uint256) {
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
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
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
            return result + (rounding == Rounding.Up && 10 ** result < value ? 1 : 0);
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
     * @dev Return the log in base 256, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result << 3) < value ? 1 : 0);
        }
    }
}


// File @openzeppelin/contracts/utils/math/SignedMath.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/SignedMath.sol)

pragma solidity ^0.8.0;

/**
 * @dev Standard signed math utilities missing in the Solidity language.
 */
library SignedMath {
    /**
     * @dev Returns the largest of two signed numbers.
     */
    function max(int256 a, int256 b) internal pure returns (int256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two signed numbers.
     */
    function min(int256 a, int256 b) internal pure returns (int256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two signed numbers without overflow.
     * The result is rounded towards zero.
     */
    function average(int256 a, int256 b) internal pure returns (int256) {
        // Formula from the book "Hacker's Delight"
        int256 x = (a & b) + ((a ^ b) >> 1);
        return x + (int256(uint256(x) >> 255) & (a ^ b));
    }

    /**
     * @dev Returns the absolute unsigned value of a signed value.
     */
    function abs(int256 n) internal pure returns (uint256) {
        unchecked {
            // must be unchecked in order to support `n = type(int256).min`
            return uint256(n >= 0 ? n : -n);
        }
    }
}


// File @openzeppelin/contracts/utils/Strings.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (utils/Strings.sol)

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
     * @dev Converts a `int256` to its ASCII `string` decimal representation.
     */
    function toString(int256 value) internal pure returns (string memory) {
        return string(abi.encodePacked(value < 0 ? "-" : "", toString(SignedMath.abs(value))));
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

    /**
     * @dev Returns true if the two strings are equal.
     */
    function equal(string memory a, string memory b) internal pure returns (bool) {
        return keccak256(bytes(a)) == keccak256(bytes(b));
    }
}


// File @openzeppelin/contracts/utils/cryptography/ECDSA.sol@v4.9.5

// Original license: SPDX_License_Identifier: MIT
// OpenZeppelin Contracts (last updated v4.9.0) (utils/cryptography/ECDSA.sol)

pragma solidity ^0.8.0;

/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 */
library ECDSA {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS,
        InvalidSignatureV // Deprecated in v4.8
    }

    function _throwError(RecoverError error) private pure {
        if (error == RecoverError.NoError) {
            return; // no error: do nothing
        } else if (error == RecoverError.InvalidSignature) {
            revert("ECDSA: invalid signature");
        } else if (error == RecoverError.InvalidSignatureLength) {
            revert("ECDSA: invalid signature length");
        } else if (error == RecoverError.InvalidSignatureS) {
            revert("ECDSA: invalid signature 's' value");
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature` or error string. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, bytes memory signature) internal pure returns (address, RecoverError) {
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            /// @solidity memory-safe-assembly
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return tryRecover(hash, v, r, s);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength);
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature`. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, signature);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `r` and `vs` short-signature fields separately.
     *
     * See https://eips.ethereum.org/EIPS/eip-2098[EIP-2098 short signatures]
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address, RecoverError) {
        bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        uint8 v = uint8((uint256(vs) >> 255) + 27);
        return tryRecover(hash, v, r, s);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `r and `vs` short-signature fields separately.
     *
     * _Available since v4.2._
     */
    function recover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, r, vs);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
     * `r` and `s` signature fields separately.
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address, RecoverError) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS);
        }

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature);
        }

        return (signer, RecoverError.NoError);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function recover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, v, r, s);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from a `hash`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes32 hash) internal pure returns (bytes32 message) {
        // 32 is the length in bytes of hash,
        // enforced by the type signature above
        /// @solidity memory-safe-assembly
        assembly {
            mstore(0x00, "\x19Ethereum Signed Message:\n32")
            mstore(0x1c, hash)
            message := keccak256(0x00, 0x3c)
        }
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from `s`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes memory s) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n", Strings.toString(s.length), s));
    }

    /**
     * @dev Returns an Ethereum Signed Typed Data, created from a
     * `domainSeparator` and a `structHash`. This produces hash corresponding
     * to the one signed with the
     * https://eips.ethereum.org/EIPS/eip-712[`eth_signTypedData`]
     * JSON-RPC method as part of EIP-712.
     *
     * See {recover}.
     */
    function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal pure returns (bytes32 data) {
        /// @solidity memory-safe-assembly
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, "\x19\x01")
            mstore(add(ptr, 0x02), domainSeparator)
            mstore(add(ptr, 0x22), structHash)
            data := keccak256(ptr, 0x42)
        }
    }

    /**
     * @dev Returns an Ethereum Signed Data with intended validator, created from a
     * `validator` and `data` according to the version 0 of EIP-191.
     *
     * See {recover}.
     */
    function toDataWithIntendedValidatorHash(address validator, bytes memory data) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x00", validator, data));
    }
}


// File contracts/orand-v2/interfaces/IOrandECDSAV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

// Error
error InvalidECDSAProofLength(uint256 proofLength);
error InvalidProofSigner(address proofSigner);

interface IOrandECDSAV2 {
  // Struct Orand ECDSA proof
  struct OrandECDSAProof {
    address signer;
    address receiverAddress;
    uint96 receiverEpoch;
    uint256 ecvrfProofDigest;
  }

  // Get signer address from a valid proof
  function decomposeProof(bytes memory proof) external pure returns (OrandECDSAProof memory ecdsaProof);

  // Get operator
  function getOperator() external view returns (address operatorAddress);
}


// File contracts/orand-v2/interfaces/IOrandProviderV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error UnableToForwardRandomness(address receiver, uint256 y);
error InvalidAlphaValue(uint256 expectedAlpha, uint256 givenAlpha);
error InvalidGenesisEpoch(uint256 currentEpoch);
error InvalidECVRFProofDigest();

interface IOrandProviderV2 is IOrandECDSAV2 {
  // ECVRF struct
  struct ECVRFProof {
    uint256[2] gamma;
    uint256 c;
    uint256 s;
    uint256 alpha;
    address uWitness;
    uint256[2] cGammaWitness;
    uint256[2] sHashWitness;
    uint256 zInv;
  }

  // Start new genesis for receiver
  function genesis(bytes memory fraudProof, ECVRFProof calldata ecvrfProof) external returns (bool);

  // Publish new epoch with Fraud Proof
  function publishFraudProof(bytes memory fraudProof, ECVRFProof calldata ecvrfProof) external returns (bool);

  // Publish new epoch with ECDSA Proof and Fraud Proof
  function publish(address receiver, ECVRFProof calldata ecvrfProof) external returns (bool);

  // Verify a ECVRF proof epoch is valid or not
  function verifyEpoch(
    bytes memory fraudProof,
    ECVRFProof calldata ecvrfProof
  )
    external
    view
    returns (
      OrandECDSAProof memory ecdsaProof,
      uint96 currentEpochNumber,
      bool isEpochLinked,
      bool isValidDualProof,
      uint256 currentEpochResult,
      uint256 verifiedEpochResult
    );

  // Get address of ECVRF verifier
  function getECVRFVerifier() external view returns (address ecvrfVerifier);
}


// File contracts/orand-v2/interfaces/IOrandECVRFV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

interface IOrandECVRFV2 {
  // Verify raw proof of ECVRF
  function verifyECVRFProof(
    uint256[2] memory pk,
    uint256[2] memory gamma,
    uint256 c,
    uint256 s,
    uint256 alpha,
    address uWitness,
    uint256[2] memory cGammaWitness,
    uint256[2] memory sHashWitness,
    uint256 zInv
  ) external view returns (uint256 y);

  // Verify structed proof of ECVRF
  function verifyStructECVRFProof(
    uint256[2] memory pk,
    IOrandProviderV2.ECVRFProof memory ecvrfProof
  ) external view returns (uint256 y);
}


// File contracts/libraries/Bytes.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;

// Index is out of range
error OutOfRange(uint256 requiredLen, uint256 maxLen);

library Bytes {
  // Read address from input bytes buffer
  function readAddress(bytes memory input, uint256 offset) internal pure returns (address result) {
    if (offset + 20 > input.length) {
      revert OutOfRange(offset + 20, input.length);
    }
    assembly {
      result := shr(96, mload(add(add(input, 0x20), offset)))
    }
  }

  // Read unsafe from input bytes buffer
  function readUintUnsafe(bytes memory input, uint256 offset, uint256 bitLen) internal pure returns (uint256 result) {
    assembly {
      result := shr(sub(256, bitLen), mload(add(add(input, 0x20), offset)))
    }
  }

  // Read uint256 from input bytes buffer
  function readUint256(bytes memory input, uint256 offset) internal pure returns (uint256 result) {
    if (offset + 32 > input.length) {
      revert OutOfRange(offset + 32, input.length);
    }
    assembly {
      result := mload(add(add(input, 0x20), offset))
    }
  }

  // Read a sub bytes array from input bytes buffer
  function readBytes(bytes memory input, uint256 offset, uint256 length) internal pure returns (bytes memory) {
    if (offset + length > input.length) {
      revert OutOfRange(offset + length, input.length);
    }
    bytes memory result = new bytes(length);
    assembly {
      // Seek offset to the beginning
      let seek := add(add(input, 0x20), offset)

      // Next is size of data
      let resultOffset := add(result, 0x20)

      for {
        let i := 0
      } lt(i, length) {
        i := add(i, 0x20)
      } {
        mstore(add(resultOffset, i), mload(add(seek, i)))
      }
    }
    return result;
  }
}


// File contracts/orand-v2/OrandECDSAV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;



contract OrandECDSAV2 is IOrandECDSAV2 {
  // Event: Set New Operator
  event SetNewOperator(address indexed oldOperator, address indexed newOperator);

  // Orand operator address
  address private operator;

  // Byte manipulation
  using Bytes for bytes;

  // Verifiy digital signature
  using ECDSA for bytes;
  using ECDSA for bytes32;

  // Set operator at constructing time
  constructor(address operatorAddress) {
    _setOperator(operatorAddress);
  }

  //=======================[  Internal  ]====================

  // Set proof operator
  function _setOperator(address operatorAddress) internal {
    emit SetNewOperator(operator, operatorAddress);
    operator = operatorAddress;
  }

  //=======================[  Internal View  ]====================

  // Get operator address
  function _getOperator() internal view returns (address operatorAddress) {
    return operator;
  }

  // Verify proof of operator
  // 0 - 65: secp256k1 Signature
  // 65 - 77: Epoch
  // 77 - 97: Receiver address
  // 97 - 129: Y result of VRF
  function _decodeFraudProof(bytes memory fraudProof) internal pure returns (OrandECDSAProof memory ecdsaProof) {
    if (fraudProof.length != 129) {
      revert InvalidECDSAProofLength(fraudProof.length);
    }
    bytes memory signature = fraudProof.readBytes(0, 65);
    bytes memory message = fraudProof.readBytes(65, fraudProof.length - 65);
    uint256 proofUint = message.readUint256(0);
    ecdsaProof.receiverEpoch = uint96(proofUint >> 160);
    ecdsaProof.receiverAddress = address(uint160(proofUint));
    ecdsaProof.ecvrfProofDigest = message.readUint256(32);
    ecdsaProof.signer = message.toEthSignedMessageHash().recover(signature);
    return ecdsaProof;
  }

  //=======================[  External View  ]====================

  // Decompose a valid proof
  function decomposeProof(bytes memory proof) external pure returns (OrandECDSAProof memory ecdsaProof) {
    return _decodeFraudProof(proof);
  }

  // Get operator
  function getOperator() external view returns (address operatorAddress) {
    return _getOperator();
  }
}


// File contracts/libraries/VRF.sol

// Original license: SPDX_License_Identifier: MIT
pragma solidity ^0.8.0;

/** ****************************************************************************
  * @notice Verification of verifiable-random-function (VRF) proofs, following
  * @notice https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.3
  * @notice See https://eprint.iacr.org/2017/099.pdf for security proofs.

  * @dev Bibliographic references:

  * @dev Goldberg, et al., "Verifiable Random Functions (VRFs)", Internet Draft
  * @dev draft-irtf-cfrg-vrf-05, IETF, Aug 11 2019,
  * @dev https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05

  * @dev Papadopoulos, et al., "Making NSEC5 Practical for DNSSEC", Cryptology
  * @dev ePrint Archive, Report 2017/099, https://eprint.iacr.org/2017/099.pdf
  * ****************************************************************************
  * @dev USAGE

  * @dev The main entry point is _randomValueFromVRFProof. See its docstring.
  * ****************************************************************************
  * @dev PURPOSE

  * @dev Reggie the Random Oracle (not his real job) wants to provide randomness
  * @dev to Vera the verifier in such a way that Vera can be sure he's not
  * @dev making his output up to suit himself. Reggie provides Vera a public key
  * @dev to which he knows the secret key. Each time Vera provides a seed to
  * @dev Reggie, he gives back a value which is computed completely
  * @dev deterministically from the seed and the secret key.

  * @dev Reggie provides a proof by which Vera can verify that the output was
  * @dev correctly computed once Reggie tells it to her, but without that proof,
  * @dev the output is computationally indistinguishable to her from a uniform
  * @dev random sample from the output space.

  * @dev The purpose of this contract is to perform that verification.
  * ****************************************************************************
  * @dev DESIGN NOTES

  * @dev The VRF algorithm verified here satisfies the full uniqueness, full
  * @dev collision resistance, and full pseudo-randomness security properties.
  * @dev See "SECURITY PROPERTIES" below, and
  * @dev https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-3

  * @dev An elliptic curve point is generally represented in the solidity code
  * @dev as a uint256[2], corresponding to its affine coordinates in
  * @dev GF(FIELD_SIZE).

  * @dev For the sake of efficiency, this implementation deviates from the spec
  * @dev in some minor ways:

  * @dev - Keccak hash rather than the SHA256 hash recommended in
  * @dev   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.5
  * @dev   Keccak costs much less gas on the EVM, and provides similar security.

  * @dev - Secp256k1 curve instead of the P-256 or ED25519 curves recommended in
  * @dev   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.5
  * @dev   For curve-point multiplication, it's much cheaper to abuse ECRECOVER

  * @dev - _hashToCurve recursively hashes until it finds a curve x-ordinate. On
  * @dev   the EVM, this is slightly more efficient than the recommendation in
  * @dev   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.4.1.1
  * @dev   step 5, to concatenate with a nonce then hash, and rehash with the
  * @dev   nonce updated until a valid x-ordinate is found.

  * @dev - _hashToCurve does not include a cipher version string or the byte 0x1
  * @dev   in the hash message, as recommended in step 5.B of the draft
  * @dev   standard. They are unnecessary here because no variation in the
  * @dev   cipher suite is allowed.

  * @dev - Similarly, the hash input in _scalarFromCurvePoints does not include a
  * @dev   commitment to the cipher suite, either, which differs from step 2 of
  * @dev   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.4.3
  * @dev   . Also, the hash input is the concatenation of the uncompressed
  * @dev   points, not the compressed points as recommended in step 3.

  * @dev - In the calculation of the challenge value "c", the "u" value (i.e.
  * @dev   the value computed by Reggie as the nonce times the secp256k1
  * @dev   generator point, see steps 5 and 7 of
  * @dev   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.3
  * @dev   ) is replaced by its ethereum address, i.e. the lower 160 bits of the
  * @dev   keccak hash of the original u. This is because we only verify the
  * @dev   calculation of u up to its address, by abusing ECRECOVER.
  * ****************************************************************************
  * @dev   SECURITY PROPERTIES

  * @dev Here are the security properties for this VRF:

  * @dev Full uniqueness: For any seed and valid VRF public key, there is
  * @dev   exactly one VRF output which can be proved to come from that seed, in
  * @dev   the sense that the proof will pass _verifyVRFProof.

  * @dev Full collision resistance: It's cryptographically infeasible to find
  * @dev   two seeds with same VRF output from a fixed, valid VRF key

  * @dev Full pseudorandomness: Absent the proofs that the VRF outputs are
  * @dev   derived from a given seed, the outputs are computationally
  * @dev   indistinguishable from randomness.

  * @dev https://eprint.iacr.org/2017/099.pdf, Appendix B contains the proofs
  * @dev for these properties.

  * @dev For secp256k1, the key validation described in section
  * @dev https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.6
  * @dev is unnecessary, because secp256k1 has cofactor 1, and the
  * @dev representation of the public key used here (affine x- and y-ordinates
  * @dev of the secp256k1 point on the standard y^2=x^3+7 curve) cannot refer to
  * @dev the point at infinity.
  * ****************************************************************************
  * @dev OTHER SECURITY CONSIDERATIONS
  *
  * @dev The seed input to the VRF could in principle force an arbitrary amount
  * @dev of work in _hashToCurve, by requiring extra rounds of hashing and
  * @dev checking whether that's yielded the x ordinate of a secp256k1 point.
  * @dev However, under the Random Oracle Model the probability of choosing a
  * @dev point which forces n extra rounds in _hashToCurve is 2⁻ⁿ. The base cost
  * @dev for calling _hashToCurve is about 25,000 gas, and each round of checking
  * @dev for a valid x ordinate costs about 15,555 gas, so to find a seed for
  * @dev which _hashToCurve would cost more than 2,017,000 gas, one would have to
  * @dev try, in expectation, about 2¹²⁸ seeds, which is infeasible for any
  * @dev foreseeable computational resources. (25,000 + 128 * 15,555 < 2,017,000.)

  * @dev Since the gas block limit for the Ethereum main net is 10,000,000 gas,
  * @dev this means it is infeasible for an adversary to prevent correct
  * @dev operation of this contract by choosing an adverse seed.

  * @dev (See TestMeasureHashToCurveGasCost for verification of the gas cost for
  * @dev _hashToCurve.)

  * @dev It may be possible to make a secure constant-time _hashToCurve function.
  * @dev See notes in _hashToCurve docstring.
*/
contract VRF {
  // See https://www.secg.org/sec2-v2.pdf, section 2.4.1, for these constants.
  // Number of points in Secp256k1
  uint256 private constant GROUP_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;
  // Prime characteristic of the galois field over which Secp256k1 is defined
  uint256 private constant FIELD_SIZE =
    // solium-disable-next-line indentation
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F;
  uint256 private constant WORD_LENGTH_BYTES = 0x20;

  // (base^exponent) % FIELD_SIZE
  // Cribbed from https://medium.com/@rbkhmrcr/precompiles-solidity-e5d29bd428c4
  function _bigModExp(uint256 base, uint256 exponent) internal view returns (uint256 exponentiation) {
    uint256 callResult;
    uint256[6] memory bigModExpContractInputs;
    bigModExpContractInputs[0] = WORD_LENGTH_BYTES; // Length of base
    bigModExpContractInputs[1] = WORD_LENGTH_BYTES; // Length of exponent
    bigModExpContractInputs[2] = WORD_LENGTH_BYTES; // Length of modulus
    bigModExpContractInputs[3] = base;
    bigModExpContractInputs[4] = exponent;
    bigModExpContractInputs[5] = FIELD_SIZE;
    uint256[1] memory output;
    assembly {
      callResult := staticcall(
        not(0), // Gas cost: no limit
        0x05, // Bigmodexp contract address
        bigModExpContractInputs,
        0xc0, // Length of input segment: 6*0x20-bytes
        output,
        0x20 // Length of output segment
      )
    }
    if (callResult == 0) {
      // solhint-disable-next-line custom-errors
      revert('bigModExp failure!');
    }
    return output[0];
  }

  // Let q=FIELD_SIZE. q % 4 = 3, ∴ x≡r^2 mod q ⇒ x^SQRT_POWER≡±r mod q.  See
  // https://en.wikipedia.org/wiki/Modular_square_root#Prime_or_prime_power_modulus
  uint256 private constant SQRT_POWER = (FIELD_SIZE + 1) >> 2;

  // Computes a s.t. a^2 = x in the field. Assumes a exists
  function _squareRoot(uint256 x) internal view returns (uint256) {
    return _bigModExp(x, SQRT_POWER);
  }

  // The value of y^2 given that (x,y) is on secp256k1.
  function _ySquared(uint256 x) internal pure returns (uint256) {
    // Curve is y^2=x^3+7. See section 2.4.1 of https://www.secg.org/sec2-v2.pdf
    uint256 xCubed = mulmod(x, mulmod(x, x, FIELD_SIZE), FIELD_SIZE);
    return addmod(xCubed, 7, FIELD_SIZE);
  }

  // True iff p is on secp256k1
  function _isOnCurve(uint256[2] memory p) internal pure returns (bool) {
    // Section 2.3.6. in https://www.secg.org/sec1-v2.pdf
    // requires each ordinate to be in [0, ..., FIELD_SIZE-1]
    // solhint-disable-next-line custom-errors
    require(p[0] < FIELD_SIZE, 'invalid x-ordinate');
    // solhint-disable-next-line custom-errors
    require(p[1] < FIELD_SIZE, 'invalid y-ordinate');
    return _ySquared(p[0]) == mulmod(p[1], p[1], FIELD_SIZE);
  }

  // Hash x uniformly into {0, ..., FIELD_SIZE-1}.
  function _fieldHash(bytes memory b) internal pure returns (uint256 x_) {
    x_ = uint256(keccak256(b));
    // Rejecting if x >= FIELD_SIZE corresponds to step 2.1 in section 2.3.4 of
    // http://www.secg.org/sec1-v2.pdf , which is part of the definition of
    // string_to_point in the IETF draft
    while (x_ >= FIELD_SIZE) {
      x_ = uint256(keccak256(abi.encodePacked(x_)));
    }
    return x_;
  }

  // Hash b to a random point which hopefully lies on secp256k1. The y ordinate
  // is always even, due to
  // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.4.1.1
  // step 5.C, which references arbitrary_string_to_point, defined in
  // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.5 as
  // returning the point with given x ordinate, and even y ordinate.
  function _newCandidateSecp256k1Point(bytes memory b) internal view returns (uint256[2] memory p) {
    unchecked {
      p[0] = _fieldHash(b);
      p[1] = _squareRoot(_ySquared(p[0]));
      if (p[1] % 2 == 1) {
        // Note that 0 <= p[1] < FIELD_SIZE
        // so this cannot wrap, we use unchecked to save gas.
        p[1] = FIELD_SIZE - p[1];
      }
    }
    return p;
  }

  // Domain-separation tag for initial hash in _hashToCurve. Corresponds to
  // vrf.go/hashToCurveHashPrefix
  uint256 internal constant HASH_TO_CURVE_HASH_PREFIX = 1;

  // Cryptographic hash function onto the curve.
  //
  // Corresponds to algorithm in section 5.4.1.1 of the draft standard. (But see
  // DESIGN NOTES above for slight differences.)
  //
  // TODO(alx): Implement a bounded-computation hash-to-curve, as described in
  // "Construction of Rational Points on Elliptic Curves over Finite Fields"
  // http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.831.5299&rep=rep1&type=pdf
  // and suggested by
  // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-01#section-5.2.2
  // (Though we can't used exactly that because secp256k1's j-invariant is 0.)
  //
  // This would greatly simplify the analysis in "OTHER SECURITY CONSIDERATIONS"
  // https://www.pivotaltracker.com/story/show/171120900
  function _hashToCurve(uint256[2] memory pk, uint256 input) internal view returns (uint256[2] memory rv) {
    rv = _newCandidateSecp256k1Point(abi.encodePacked(HASH_TO_CURVE_HASH_PREFIX, pk, input));
    while (!_isOnCurve(rv)) {
      rv = _newCandidateSecp256k1Point(abi.encodePacked(rv[0]));
    }
    return rv;
  }

  /** *********************************************************************
   * @notice Check that product==scalar*multiplicand
   *
   * @dev Based on Vitalik Buterin's idea in ethresear.ch post cited below.
   *
   * @param multiplicand: secp256k1 point
   * @param scalar: non-zero GF(GROUP_ORDER) scalar
   * @param product: secp256k1 expected to be multiplier * multiplicand
   * @return verifies true iff product==scalar*multiplicand, with cryptographically high probability
   */
  function _ecmulVerify(
    uint256[2] memory multiplicand,
    uint256 scalar,
    uint256[2] memory product
  ) internal pure returns (bool verifies) {
    // solhint-disable-next-line custom-errors
    require(scalar != 0, 'zero scalar'); // Rules out an ecrecover failure case
    uint256 x = multiplicand[0]; // x ordinate of multiplicand
    uint8 v = multiplicand[1] % 2 == 0 ? 27 : 28; // parity of y ordinate
    // https://ethresear.ch/t/you-can-kinda-abuse-ecrecover-to-do-ecmul-in-secp256k1-today/2384/9
    // Point corresponding to address ecrecover(0, v, x, s=scalar*x) is
    // (x⁻¹ mod GROUP_ORDER) * (scalar * x * multiplicand - 0 * g), i.e.
    // scalar*multiplicand. See https://crypto.stackexchange.com/a/18106
    bytes32 scalarTimesX = bytes32(mulmod(scalar, x, GROUP_ORDER));
    address actual = ecrecover(bytes32(0), v, bytes32(x), scalarTimesX);
    // Explicit conversion to address takes bottom 160 bits
    address expected = address(uint160(uint256(keccak256(abi.encodePacked(product)))));
    return (actual == expected);
  }

  // Returns x1/z1-x2/z2=(x1z2-x2z1)/(z1z2) in projective coordinates on P¹(𝔽ₙ)
  function _projectiveSub(
    uint256 x1,
    uint256 z1,
    uint256 x2,
    uint256 z2
  ) internal pure returns (uint256 x3, uint256 z3) {
    unchecked {
      uint256 num1 = mulmod(z2, x1, FIELD_SIZE);
      // Note this cannot wrap since x2 is a point in [0, FIELD_SIZE-1]
      // we use unchecked to save gas.
      uint256 num2 = mulmod(FIELD_SIZE - x2, z1, FIELD_SIZE);
      (x3, z3) = (addmod(num1, num2, FIELD_SIZE), mulmod(z1, z2, FIELD_SIZE));
    }
    return (x3, z3);
  }

  // Returns x1/z1*x2/z2=(x1x2)/(z1z2), in projective coordinates on P¹(𝔽ₙ)
  function _projectiveMul(
    uint256 x1,
    uint256 z1,
    uint256 x2,
    uint256 z2
  ) internal pure returns (uint256 x3, uint256 z3) {
    (x3, z3) = (mulmod(x1, x2, FIELD_SIZE), mulmod(z1, z2, FIELD_SIZE));
    return (x3, z3);
  }

  /** **************************************************************************
        @notice Computes elliptic-curve sum, in projective co-ordinates

        @dev Using projective coordinates avoids costly divisions

        @dev To use this with p and q in affine coordinates, call
        @dev _projectiveECAdd(px, py, qx, qy). This will return
        @dev the addition of (px, py, 1) and (qx, qy, 1), in the
        @dev secp256k1 group.

        @dev This can be used to calculate the z which is the inverse to zInv
        @dev in isValidVRFOutput. But consider using a faster
        @dev re-implementation such as ProjectiveECAdd in the golang vrf package.

        @dev This function assumes [px,py,1],[qx,qy,1] are valid projective
             coordinates of secp256k1 points. That is safe in this contract,
             because this method is only used by _linearCombination, which checks
             points are on the curve via ecrecover.
        **************************************************************************
        @param px The first affine coordinate of the first summand
        @param py The second affine coordinate of the first summand
        @param qx The first affine coordinate of the second summand
        @param qy The second affine coordinate of the second summand

        (px,py) and (qx,qy) must be distinct, valid secp256k1 points.
        **************************************************************************
        Return values are projective coordinates of [px,py,1]+[qx,qy,1] as points
        on secp256k1, in P²(𝔽ₙ)
        @return sx
        @return sy
        @return sz
    */
  function _projectiveECAdd(
    uint256 px,
    uint256 py,
    uint256 qx,
    uint256 qy
  ) internal pure returns (uint256 sx, uint256 sy, uint256 sz) {
    unchecked {
      // See "Group law for E/K : y^2 = x^3 + ax + b", in section 3.1.2, p. 80,
      // "Guide to Elliptic Curve Cryptography" by Hankerson, Menezes and Vanstone
      // We take the equations there for (sx,sy), and homogenize them to
      // projective coordinates. That way, no inverses are required, here, and we
      // only need the one inverse in _affineECAdd.

      // We only need the "point addition" equations from Hankerson et al. Can
      // skip the "point doubling" equations because p1 == p2 is cryptographically
      // impossible, and required not to be the case in _linearCombination.

      // Add extra "projective coordinate" to the two points
      (uint256 z1, uint256 z2) = (1, 1);

      // (lx, lz) = (qy-py)/(qx-px), i.e., gradient of secant line.
      // Cannot wrap since px and py are in [0, FIELD_SIZE-1]
      uint256 lx = addmod(qy, FIELD_SIZE - py, FIELD_SIZE);
      uint256 lz = addmod(qx, FIELD_SIZE - px, FIELD_SIZE);

      uint256 dx; // Accumulates denominator from sx calculation
      // sx=((qy-py)/(qx-px))^2-px-qx
      (sx, dx) = _projectiveMul(lx, lz, lx, lz); // ((qy-py)/(qx-px))^2
      (sx, dx) = _projectiveSub(sx, dx, px, z1); // ((qy-py)/(qx-px))^2-px
      (sx, dx) = _projectiveSub(sx, dx, qx, z2); // ((qy-py)/(qx-px))^2-px-qx

      uint256 dy; // Accumulates denominator from sy calculation
      // sy=((qy-py)/(qx-px))(px-sx)-py
      (sy, dy) = _projectiveSub(px, z1, sx, dx); // px-sx
      (sy, dy) = _projectiveMul(sy, dy, lx, lz); // ((qy-py)/(qx-px))(px-sx)
      (sy, dy) = _projectiveSub(sy, dy, py, z1); // ((qy-py)/(qx-px))(px-sx)-py

      if (dx != dy) {
        // Cross-multiply to put everything over a common denominator
        sx = mulmod(sx, dy, FIELD_SIZE);
        sy = mulmod(sy, dx, FIELD_SIZE);
        sz = mulmod(dx, dy, FIELD_SIZE);
      } else {
        // Already over a common denominator, use that for z ordinate
        sz = dx;
      }
    }
    return (sx, sy, sz);
  }

  // p1+p2, as affine points on secp256k1.
  //
  // invZ must be the inverse of the z returned by _projectiveECAdd(p1, p2).
  // It is computed off-chain to save gas.
  //
  // p1 and p2 must be distinct, because _projectiveECAdd doesn't handle
  // point doubling.
  function _affineECAdd(
    uint256[2] memory p1,
    uint256[2] memory p2,
    uint256 invZ
  ) internal pure returns (uint256[2] memory) {
    uint256 x;
    uint256 y;
    uint256 z;
    (x, y, z) = _projectiveECAdd(p1[0], p1[1], p2[0], p2[1]);
    // solhint-disable-next-line custom-errors
    require(mulmod(z, invZ, FIELD_SIZE) == 1, 'invZ must be inverse of z');
    // Clear the z ordinate of the projective representation by dividing through
    // by it, to obtain the affine representation
    return [mulmod(x, invZ, FIELD_SIZE), mulmod(y, invZ, FIELD_SIZE)];
  }

  // True iff address(c*p+s*g) == lcWitness, where g is generator. (With
  // cryptographically high probability.)
  function _verifyLinearCombinationWithGenerator(
    uint256 c,
    uint256[2] memory p,
    uint256 s,
    address lcWitness
  ) internal pure returns (bool) {
    // Rule out ecrecover failure modes which return address 0.
    unchecked {
      // solhint-disable-next-line custom-errors
      require(lcWitness != address(0), 'bad witness');
      uint8 v = (p[1] % 2 == 0) ? 27 : 28; // parity of y-ordinate of p
      // Note this cannot wrap (X - Y % X), but we use unchecked to save
      // gas.
      bytes32 pseudoHash = bytes32(GROUP_ORDER - mulmod(p[0], s, GROUP_ORDER)); // -s*p[0]
      bytes32 pseudoSignature = bytes32(mulmod(c, p[0], GROUP_ORDER)); // c*p[0]
      // https://ethresear.ch/t/you-can-kinda-abuse-ecrecover-to-do-ecmul-in-secp256k1-today/2384/9
      // The point corresponding to the address returned by
      // ecrecover(-s*p[0],v,p[0],c*p[0]) is
      // (p[0]⁻¹ mod GROUP_ORDER)*(c*p[0]-(-s)*p[0]*g)=c*p+s*g.
      // See https://crypto.stackexchange.com/a/18106
      // https://bitcoin.stackexchange.com/questions/38351/ecdsa-v-r-s-what-is-v
      address computed = ecrecover(pseudoHash, v, bytes32(p[0]), pseudoSignature);
      return computed == lcWitness;
    }
  }

  // c*p1 + s*p2. Requires cp1Witness=c*p1 and sp2Witness=s*p2. Also
  // requires cp1Witness != sp2Witness (which is fine for this application,
  // since it is cryptographically impossible for them to be equal. In the
  // (cryptographically impossible) case that a prover accidentally derives
  // a proof with equal c*p1 and s*p2, they should retry with a different
  // proof nonce.) Assumes that all points are on secp256k1
  // (which is checked in _verifyVRFProof below.)
  function _linearCombination(
    uint256 c,
    uint256[2] memory p1,
    uint256[2] memory cp1Witness,
    uint256 s,
    uint256[2] memory p2,
    uint256[2] memory sp2Witness,
    uint256 zInv
  ) internal pure returns (uint256[2] memory) {
    unchecked {
      // Note we are relying on the wrap around here
      // solhint-disable-next-line custom-errors
      require((cp1Witness[0] % FIELD_SIZE) != (sp2Witness[0] % FIELD_SIZE), 'points in sum must be distinct');
      // solhint-disable-next-line custom-errors
      require(_ecmulVerify(p1, c, cp1Witness), 'First mul check failed');
      // solhint-disable-next-line custom-errors
      require(_ecmulVerify(p2, s, sp2Witness), 'Second mul check failed');
      return _affineECAdd(cp1Witness, sp2Witness, zInv);
    }
  }

  // Domain-separation tag for the hash taken in _scalarFromCurvePoints.
  // Corresponds to scalarFromCurveHashPrefix in vrf.go
  uint256 internal constant SCALAR_FROM_CURVE_POINTS_HASH_PREFIX = 2;

  // Pseudo-random number from inputs. Matches vrf.go/_scalarFromCurvePoints, and
  // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-vrf-05#section-5.4.3
  // The draft calls (in step 7, via the definition of string_to_int, in
  // https://datatracker.ietf.org/doc/html/rfc8017#section-4.2 ) for taking the
  // first hash without checking that it corresponds to a number less than the
  // group order, which will lead to a slight bias in the sample.
  //
  // TODO(alx): We could save a bit of gas by following the standard here and
  // using the compressed representation of the points, if we collated the y
  // parities into a single bytes32.
  // https://www.pivotaltracker.com/story/show/171120588
  function _scalarFromCurvePoints(
    uint256[2] memory hash,
    uint256[2] memory pk,
    uint256[2] memory gamma,
    address uWitness,
    uint256[2] memory v
  ) internal pure returns (uint256 s) {
    return uint256(keccak256(abi.encodePacked(SCALAR_FROM_CURVE_POINTS_HASH_PREFIX, hash, pk, gamma, v, uWitness)));
  }

  // True if (gamma, c, s) is a correctly constructed randomness proof from pk
  // and seed. zInv must be the inverse of the third ordinate from
  // _projectiveECAdd applied to cGammaWitness and sHashWitness. Corresponds to
  // section 5.3 of the IETF draft.
  //
  // TODO(alx): Since I'm only using pk in the ecrecover call, I could only pass
  // the x ordinate, and the parity of the y ordinate in the top bit of uWitness
  // (which I could make a uint256 without using any extra space.) Would save
  // about 2000 gas. https://www.pivotaltracker.com/story/show/170828567
  function _verifyVRFProof(
    uint256[2] memory pk,
    uint256[2] memory gamma,
    uint256 c,
    uint256 s,
    uint256 seed,
    address uWitness,
    uint256[2] memory cGammaWitness,
    uint256[2] memory sHashWitness,
    uint256 zInv
  ) internal view {
    unchecked {
      // solhint-disable-next-line custom-errors
      require(_isOnCurve(pk), 'public key is not on curve');
      // solhint-disable-next-line custom-errors
      require(_isOnCurve(gamma), 'gamma is not on curve');
      // solhint-disable-next-line custom-errors
      require(_isOnCurve(cGammaWitness), 'cGammaWitness is not on curve');
      // solhint-disable-next-line custom-errors
      require(_isOnCurve(sHashWitness), 'sHashWitness is not on curve');
      // Step 5. of IETF draft section 5.3 (pk corresponds to 5.3's Y, and here
      // we use the address of u instead of u itself. Also, here we add the
      // terms instead of taking the difference, and in the proof construction in
      // vrf.GenerateProof, we correspondingly take the difference instead of
      // taking the sum as they do in step 7 of section 5.1.)
      // solhint-disable-next-line custom-errors
      require(_verifyLinearCombinationWithGenerator(c, pk, s, uWitness), 'addr(c*pk+s*g)!=_uWitness');
      // Step 4. of IETF draft section 5.3 (pk corresponds to Y, seed to alpha_string)
      uint256[2] memory hash = _hashToCurve(pk, seed);
      // Step 6. of IETF draft section 5.3, but see note for step 5 about +/- terms
      uint256[2] memory v = _linearCombination(c, gamma, cGammaWitness, s, hash, sHashWitness, zInv);
      // Steps 7. and 8. of IETF draft section 5.3
      uint256 derivedC = _scalarFromCurvePoints(hash, pk, gamma, uWitness, v);
      // solhint-disable-next-line custom-errors
      require(c == derivedC, 'invalid proof');
    }
  }

  // Domain-separation tag for the hash used as the final VRF output.
  // Corresponds to vrfRandomOutputHashPrefix in vrf.go
  uint256 internal constant VRF_RANDOM_OUTPUT_HASH_PREFIX = 3;

  struct Proof {
    uint256[2] pk;
    uint256[2] gamma;
    uint256 c;
    uint256 s;
    uint256 seed;
    address uWitness;
    uint256[2] cGammaWitness;
    uint256[2] sHashWitness;
    uint256 zInv;
  }

  /* ***************************************************************************
     * @notice Returns proof's output, if proof is valid. Otherwise reverts

     * @param proof vrf proof components
     * @param seed  seed used to generate the vrf output
     *
     * Throws if proof is invalid, otherwise:
     * @return output i.e., the random output implied by the proof
     * ***************************************************************************
     */
  function _randomValueFromVRFProof(Proof memory proof, uint256 seed) internal view returns (uint256 output) {
    _verifyVRFProof(
      proof.pk,
      proof.gamma,
      proof.c,
      proof.s,
      seed,
      proof.uWitness,
      proof.cGammaWitness,
      proof.sHashWitness,
      proof.zInv
    );
    output = uint256(keccak256(abi.encode(VRF_RANDOM_OUTPUT_HASH_PREFIX, proof.gamma)));
    return output;
  }
}


// File contracts/orand-v2/OrandECVRFV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;


contract OrandECVRFV2 is VRF, IOrandECVRFV2 {
  // Verify raw proof of ECVRF
  function verifyECVRFProof(
    uint256[2] memory pk,
    uint256[2] memory gamma,
    uint256 c,
    uint256 s,
    uint256 alpha,
    address uWitness,
    uint256[2] memory cGammaWitness,
    uint256[2] memory sHashWitness,
    uint256 zInv
  ) external view returns (uint256 y) {
    _verifyVRFProof(pk, gamma, c, s, alpha, uWitness, cGammaWitness, sHashWitness, zInv);
    return uint256(keccak256(abi.encode(gamma)));
  }

  // Verify structed proof of ECVRF
  function verifyStructECVRFProof(
    uint256[2] memory pk,
    IOrandProviderV2.ECVRFProof memory ecvrfProof
  ) external view returns (uint256 y) {
    _verifyVRFProof(
      pk,
      ecvrfProof.gamma,
      ecvrfProof.c,
      ecvrfProof.s,
      ecvrfProof.alpha,
      ecvrfProof.uWitness,
      ecvrfProof.cGammaWitness,
      ecvrfProof.sHashWitness,
      ecvrfProof.zInv
    );
    return uint256(keccak256(abi.encode(ecvrfProof.gamma)));
  }
}


// File contracts/orand-v2/interfaces/IOrandManagementV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

interface IOrandManagementV2 {
  // Get public key
  function getPublicKey() external view returns (uint256[2] memory pubKey);

  // Get digest of corresponding public key
  function getPublicKeyDigest() external view returns (bytes32 operator);
}


// File contracts/orand-v2/OrandManagementV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;


contract OrandManagementV2 is IOrandManagementV2 {
  // Public key that will be use to
  uint256[2] private publicKey;

  // Event Set New Public Key
  event SetNewPublicKey(address indexed actor, uint256 indexed pkx, uint256 indexed pky);

  // Set public key of Orand at the constructing time
  constructor(uint256[2] memory publickey) {
    _setPublicKey(publickey);
  }

  //=======================[  Internal  ]====================

  // Set new public key by XY to verify ECVRF proof
  function _setPublicKey(uint256[2] memory publickey) internal {
    publicKey = publickey;
    emit SetNewPublicKey(msg.sender, publickey[0], publickey[1]);
  }

  //=======================[  Internal view ]====================

  // Get public key
  function _getPublicKey() internal view returns (uint256[2] memory pubKey) {
    return publicKey;
  }

  // Get public key digest
  function _getPublicKeyDigest() internal view returns (bytes32 pubKeyDigest) {
    return keccak256(abi.encodePacked(publicKey));
  }

  //=======================[  External view  ]====================

  // Get public key
  function getPublicKey() external view returns (uint256[2] memory pubKey) {
    return _getPublicKey();
  }

  // Get digest of corresponding public key
  function getPublicKeyDigest() external view returns (bytes32 operator) {
    return _getPublicKeyDigest();
  }
}


// File contracts/orand-v2/interfaces/IOrandConsumerV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error InvalidProvider();

interface IOrandConsumerV2 {
  // Consume the verifiable randomness from Orand provider
  // Return false if you want to stop batching
  function consumeRandomness(uint256 randomness) external returns (bool);
}


// File contracts/orand-v2/interfaces/IOrandStorageV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

interface IOrandStorageV2 {
  // Get a given epoch result for a given receiver
  function getEpochResult(address receiver, uint96 epoch) external view returns (uint256 result);

  // Get total number of epochs for a given receiver
  function getTotalEpoch(address receiver) external view returns (uint96 epoch);

  // Get current epoch of a given receiver
  function getCurrentEpoch(address receiver) external view returns (uint96 epoch);

  // Get current epoch of a given receiver
  function getCurrentEpochResult(address receiver) external view returns (uint256 result);
}


// File contracts/orand-v2/OrandStorageV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;


contract OrandStorageV2 is IOrandStorageV2 {
  using Bytes for bytes;

  // Event: New Epoch
  event NewEpoch(address indexed receiverAddress, uint96 indexed receiverEpoch, uint256 indexed randomness);

  // Storage of recent epoch's result
  // Map epoch ++ receiver  -> alpha
  mapping(uint256 => uint256) private epochResult;

  // Map receiver -> total epoch
  mapping(address => uint256) private epochMax;

  //=======================[  Internal  ]====================

  // Add validity epoch
  function _addEpoch(address receiver, uint256 result) internal {
    uint96 epoch = uint96(epochMax[receiver]);
    // Add epoch to storage
    // epoch != 0 => able to sue == true
    epochResult[_packing(epoch, receiver)] = result;
    // If add new epoch we increase the epoch max 1
    epochMax[receiver] = epoch + 1;
    // Emit event to outside of EVM
    emit NewEpoch(receiver, epoch, result);
  }

  //=======================[  Internal pure ]====================

  // Packing adderss and uint96 to a single bytes32
  // 96 bits a ++ 160 bits b
  function _packing(uint96 a, address b) internal pure returns (uint256 packed) {
    assembly {
      packed := or(shl(160, a), b)
    }
  }

  //=======================[  Internal View  ]====================

  // Get result of current epoch
  function _getCurrentEpoch(address receiver) internal view returns (uint96 epoch) {
    epoch = uint96(epochMax[receiver]);
    return (epoch > 0) ? epoch - 1 : epoch;
  }

  // Get total number of epoch for a given receiver
  function _getTotalEpoch(address receiver) internal view returns (uint96 epoch) {
    return uint96(epochMax[receiver]);
  }

  // Get result of current epoch
  function _getCurrentEpochResult(address receiver) internal view returns (uint256 result) {
    return epochResult[_packing(_getCurrentEpoch(receiver), receiver)];
  }

  //=======================[  External View  ]====================

  // Get a given epoch result for a given receiver
  function getEpochResult(address receiver, uint96 epoch) external view returns (uint256 result) {
    return epochResult[_packing(epoch, receiver)];
  }

  // Get current epoch of a given receiver
  function getCurrentEpochResult(address receiver) external view returns (uint256 result) {
    return _getCurrentEpochResult(receiver);
  }

  // Get total number of epochs for a given receiver
  function getTotalEpoch(address receiver) external view returns (uint96 epoch) {
    return _getTotalEpoch(receiver);
  }

  // Get current epoch of a given receiver
  function getCurrentEpoch(address receiver) external view returns (uint96 epoch) {
    return _getCurrentEpoch(receiver);
  }
}


// File contracts/orocle-v1/interfaces/IOrocleAggregatorV1.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error ExistedApplication(uint32 appId);
error InvalidApplication(uint32 appId);
error InvalidApplicationName(bytes24 appName);
error InvalidRoundNumber(uint64 round, uint64 requiredRound);
error UndefinedRound(uint64 round);
error InvalidDataLength(uint256 length);
error UnableToPublishData(bytes data);
error DeactivatedUser(address user);

interface IOrocleAggregatorV1 {
  /**
   * Emit event when a new request is created
   * @param identifier Data identifier
   * @param data Data
   */
  function request(uint256 identifier, bytes calldata data) external returns (bool);

  /**
   * Fulfill request
   * @param identifier Data identifier
   * @param data Data
   */
  function fulfill(uint256 identifier, bytes calldata data) external returns (bool);

  /**
   * Check if user is deactivated
   * @param user User address
   * @return status
   */
  function isDeactivated(address user) external view returns (bool);

  /**
   * Get round of a given application
   * @param appId Application ID
   * @return round
   */
  function getMetadata(uint32 appId, bytes20 identifier) external view returns (uint64 round, uint64 lastUpdate);

  /**
   * Get data of an application
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getData(uint32 appId, uint64 round, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return data
   */
  function getLatestData(uint32 appId, bytes20 identifier) external view returns (bytes32 data);

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return round lastUpdate data
   */
  function getLatestRound(
    uint32 appId,
    bytes20 identifier
  ) external view returns (uint64 round, uint64 lastUpdate, bytes32 data);
}


// File contracts/orand-v2/OrandProviderV2.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity 0.8.19;








contract OrandProviderV2 is IOrandProviderV2, Ownable, OrandStorageV2, OrandManagementV2, OrandECDSAV2 {
  // ECVRF verifier smart contract
  IOrandECVRFV2 private ecvrf;

  // Orocle V1
  IOrocleAggregatorV1 private oracle;

  // We allow max batching is 1000
  uint256 private maxBatching;

  // Event: Set New ECVRF Verifier
  event SetNewECVRFVerifier(address indexed actor, address indexed ecvrfAddress);

  // Event: Set the limit for batching randomness
  event SetBatchingLimit(address indexed actor, uint256 indexed maxBatching);

  // Event: set new oracle
  event SetNewOracle(address indexed actor, address indexed newOracle);

  // Provider V2 construct method
  constructor(
    uint256[2] memory publicKey,
    address operator,
    address ecvrfAddress,
    address oracleAddress,
    uint256 maxBatchingLimit
  ) OrandManagementV2(publicKey) OrandECDSAV2(operator) {
    _setNewECVRFVerifier(ecvrfAddress);
    _setNewOracle(oracleAddress);
    _setMaxBatching(maxBatchingLimit);
  }

  //=======================[  Owner  ]====================

  // Update new ECVRF verifier
  function setMaxBatching(uint256 maxBatchingLimit) external onlyOwner returns (bool) {
    _setMaxBatching(maxBatchingLimit);
    return true;
  }

  // Update new ECVRF verifier
  function setNewOracle(address oracleAddress) external onlyOwner returns (bool) {
    _setNewOracle(oracleAddress);
    return true;
  }

  // Update new ECVRF verifier
  function setNewECVRFVerifier(address ecvrfAddress) external onlyOwner returns (bool) {
    _setNewECVRFVerifier(ecvrfAddress);
    return true;
  }

  // Set new public key to verify proof
  function setPublicKey(uint256[2] memory pk) external onlyOwner returns (bool) {
    _setPublicKey(pk);
    return true;
  }

  //=======================[  Internal  ]====================

  // Update new ECVRF verifier
  function _setMaxBatching(uint256 maxBatchingLimit) internal {
    maxBatching = maxBatchingLimit;
    emit SetBatchingLimit(msg.sender, maxBatchingLimit);
  }

  // Update new ECVRF verifier
  function _setNewOracle(address oracleAddress) internal {
    oracle = IOrocleAggregatorV1(oracleAddress);
    emit SetNewOracle(msg.sender, oracleAddress);
  }

  // Update new ECVRF verifier
  function _setNewECVRFVerifier(address ecvrfAddress) internal {
    ecvrf = IOrandECVRFV2(ecvrfAddress);
    emit SetNewECVRFVerifier(msg.sender, ecvrfAddress);
  }

  //=======================[  External  ]====================

  // Start new genesis for receiver
  function genesis(bytes memory fraudProof, ECVRFProof calldata ecvrfProof) external returns (bool) {
    OrandECDSAProof memory ecdsaProof = _decodeFraudProof(fraudProof);
    uint256 currentEpochResult = _getCurrentEpochResult(ecdsaProof.receiverAddress);

    // Invalid genesis epoch
    if (currentEpochResult != 0 || ecdsaProof.receiverEpoch != 0) {
      revert InvalidGenesisEpoch(currentEpochResult);
    }

    // ECVRF proof digest must match
    if (
      ecdsaProof.ecvrfProofDigest !=
      uint256(
        keccak256(
          abi.encodePacked(
            _getPublicKey(),
            ecvrfProof.gamma,
            ecvrfProof.c,
            ecvrfProof.s,
            ecvrfProof.alpha,
            ecvrfProof.uWitness,
            ecvrfProof.cGammaWitness,
            ecvrfProof.sHashWitness,
            ecvrfProof.zInv
          )
        )
      )
    ) {
      revert InvalidECVRFProofDigest();
    }

    // y = keccak256(gamma.x, gamma.y)
    // uint256 y = uint256(keccak256(abi.encodePacked(ecvrfProof.gamma)));
    uint256 result = ecvrf.verifyStructECVRFProof(_getPublicKey(), ecvrfProof);

    // Add epoch to the epoch chain of Orand ECVRF
    _addEpoch(ecdsaProof.receiverAddress, result);

    return true;
  }

  // Publish new epoch with Fraud Proof
  function publishFraudProof(bytes memory fraudProof, ECVRFProof calldata ecvrfProof) external returns (bool) {
    OrandECDSAProof memory ecdsaProof = _decodeFraudProof(fraudProof);
    uint256 currentEpochResult = _getCurrentEpochResult(ecdsaProof.receiverAddress);

    // Current alpha must be the result of previous epoch
    if (ecdsaProof.signer != _getOperator()) {
      revert InvalidProofSigner(ecdsaProof.signer);
    }

    // Current alpha must be the result of previous epoch
    if (ecvrfProof.alpha != currentEpochResult) {
      revert InvalidAlphaValue(currentEpochResult, ecvrfProof.alpha);
    }

    // ECVRF proof digest must match
    if (
      ecdsaProof.ecvrfProofDigest !=
      uint256(
        keccak256(
          abi.encodePacked(
            _getPublicKey(),
            ecvrfProof.gamma,
            ecvrfProof.c,
            ecvrfProof.s,
            ecvrfProof.alpha,
            ecvrfProof.uWitness,
            ecvrfProof.cGammaWitness,
            ecvrfProof.sHashWitness,
            ecvrfProof.zInv
          )
        )
      )
    ) {
      revert InvalidECVRFProofDigest();
    }

    // y = keccak256(gamma.x, gamma.y)
    uint256 result = uint256(keccak256(abi.encodePacked(ecvrfProof.gamma)));

    // Add epoch to the epoch chain of Orand ECVRF
    _addEpoch(ecdsaProof.receiverAddress, result);

    // Check for the existing smart contract and forward randomness to receiver
    if (ecdsaProof.receiverAddress.code.length > 0) {
      for (uint256 i = 0; i < maxBatching; i += 1) {
        if (!IOrandConsumerV2(ecdsaProof.receiverAddress).consumeRandomness(result)) {
          oracle.fulfill(0, abi.encodePacked(ecdsaProof.receiverAddress));
          break;
        }
        result = uint256(keccak256(abi.encodePacked(result)));
      }
    }

    return true;
  }

  // Publish new epoch with ECDSA Proof and Fraud Proof
  function publish(address receiver, ECVRFProof calldata ecvrfProof) external returns (bool) {
    uint256 currentEpochResult = _getCurrentEpochResult(receiver);

    // Current alpha must be the result of previous epoch
    if (ecvrfProof.alpha != currentEpochResult) {
      revert InvalidAlphaValue(currentEpochResult, ecvrfProof.alpha);
    }

    // y = keccak256(gamma.x, gamma.y)
    // uint256 y = uint256(keccak256(abi.encodePacked(ecvrfProof.gamma)));
    uint256 result = ecvrf.verifyStructECVRFProof(_getPublicKey(), ecvrfProof);

    // Add epoch to the epoch chain of Orand ECVRF
    _addEpoch(receiver, result);

    // Check for the existing smart contract and forward randomness to receiver
    if (receiver.code.length > 0) {
      for (uint256 i = 0; i < maxBatching; i += 1) {
        if (!IOrandConsumerV2(receiver).consumeRandomness(result)) {
          oracle.fulfill(0, abi.encodePacked(receiver));
          break;
        }
        result = uint256(keccak256(abi.encodePacked(result)));
      }
    }

    return true;
  }

  //=======================[  External View  ]====================

  // Verify a ECVRF proof epoch is valid or not
  function verifyEpoch(
    bytes memory fraudProof,
    ECVRFProof calldata ecvrfProof
  )
    external
    view
    returns (
      OrandECDSAProof memory ecdsaProof,
      uint96 currentEpochNumber,
      bool isEpochLinked,
      bool isValidDualProof,
      uint256 currentEpochResult,
      uint256 verifiedEpochResult
    )
  {
    ecdsaProof = _decodeFraudProof(fraudProof);

    isValidDualProof =
      ecdsaProof.ecvrfProofDigest ==
      uint256(
        keccak256(
          abi.encodePacked(
            _getPublicKey(),
            ecvrfProof.gamma,
            ecvrfProof.c,
            ecvrfProof.s,
            ecvrfProof.alpha,
            ecvrfProof.uWitness,
            ecvrfProof.cGammaWitness,
            ecvrfProof.sHashWitness,
            ecvrfProof.zInv
          )
        )
      );

    currentEpochNumber = _getCurrentEpoch(ecdsaProof.receiverAddress);
    currentEpochResult = _getCurrentEpochResult(ecdsaProof.receiverAddress);
    isEpochLinked = currentEpochResult == ecvrfProof.alpha;

    // y = keccak256(gamma.x, gamma.y)
    // uint256 y = uint256(keccak256(abi.encodePacked(ecvrfProof.gamma)));
    verifiedEpochResult = ecvrf.verifyStructECVRFProof(_getPublicKey(), ecvrfProof);
  }

  // Get address of ECVRF verifier
  function getECVRFVerifier() external view returns (address ecvrfVerifier) {
    return address(ecvrf);
  }

  // Get address of Oracle
  function getOracle() external view returns (address oracleAddress) {
    return address(oracle);
  }

  // Get maximum batching limit
  function getMaximumBatching() external view returns (uint256 maxBatchingLimit) {
    return maxBatching;
  }
}


// File contracts/orocle-v1/Operatable.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;

error InvalidOperator(address sender);

contract Operatable {
  mapping(address => bool) private operator;

  event AddOperator(address indexed newOperator);
  event RemoveOperator(address indexed OldOperator);

  modifier onlyOperator() {
    if (!operator[msg.sender]) {
      revert InvalidOperator(msg.sender);
    }
    _;
  }

  function _addOperator(address newOperator) internal returns (bool) {
    operator[newOperator] = true;
    emit AddOperator(newOperator);
    return true;
  }

  function _removeOperator(address oldOperator) internal returns (bool) {
    operator[oldOperator] = false;
    emit RemoveOperator(oldOperator);
    return true;
  }

  function _isOperator(address checkAddress) internal view returns (bool) {
    return operator[checkAddress];
  }

  function isOperator(address checkAddress) external view returns (bool) {
    return _isOperator(checkAddress);
  }
}


// File contracts/orocle-v1/OrocleV1.sol

// Original license: SPDX_License_Identifier: Apache-2.0
pragma solidity ^0.8.0;




contract OrocleV1 is IOrocleAggregatorV1, Ownable, Operatable {
  using Bytes for bytes;

  // Maping unique fingerprint to data
  mapping(bytes32 => bytes32) private database;

  // Mapping application ID ++ identifier to application metadata
  mapping(bytes32 => bytes32) private metadata;

  // Deactivated user
  mapping(address => bool) private deactivated;

  // Publish new data
  event PublishData(uint32 indexed application, uint64 indexed round, bytes20 indexed identifier, bytes32 data);

  // Request new data
  event Request(address indexed actor, uint256 indexed identifier, bytes indexed data);

  // Fulfill request
  event FulFill(address indexed actor, uint256 indexed identifier, bytes indexed data);

  // Deactivated user status update
  event Deactivated(address indexed actor, bool indexed status);

  // Only active user
  modifier onlyActive() {
    if (deactivated[msg.sender]) {
      revert DeactivatedUser(msg.sender);
    }
    _;
  }

  /**
   * Create new oracle
   */
  constructor(address[] memory operatorList) {
    for (uint256 i = 0; i < operatorList.length; i += 1) {
      _addOperator(operatorList[i]);
    }
  }

  //=======================[  External  ]====================

  /**
   * Emit event when a new request is created
   * @param identifier Data identifier
   * @param data Data
   */
  function request(uint256 identifier, bytes calldata data) external returns (bool) {
    emit Request(msg.sender, identifier, data);
    return true;
  }

  /**
   * Fulfill request
   * @param identifier Data identifier
   * @param data Data
   */
  function fulfill(uint256 identifier, bytes calldata data) external returns (bool) {
    emit FulFill(msg.sender, identifier, data);
    return true;
  }

  //=======================[  Owner  ]====================

  /**
   * Set new operator
   * @param newOperator New operator address
   * @return success
   */
  function addOperator(address newOperator) external onlyOwner returns (bool) {
    return _addOperator(newOperator);
  }

  /**
   * Remove old operator
   * @param oldOperator New operator address
   * @return success
   */
  function removeOperator(address oldOperator) external onlyOwner returns (bool) {
    return _removeOperator(oldOperator);
  }

  //=======================[  Operator  ]====================

  // Set deactivated status
  function setDeactivatedStatus(address userAddress, bool status) external onlyOperator returns (bool) {
    _setDeactivateStatus(userAddress, status);
    return true;
  }

  /**
   * Publish data to database
   * @param packedData packed data
   * @return success
   */
  function publishData(uint32 appId, bytes memory packedData) external onlyOperator returns (bool) {
    // Decode appId and chunksize
    bytes20 identifier;
    bytes32 data;
    if (packedData.length % 52 != 0) {
      revert InvalidDataLength(packedData.length);
    }
    for (uint256 i = 0; i < packedData.length; i += 52) {
      identifier = bytes20(uint160(packedData.readUintUnsafe(i, 160)));
      data = bytes32(uint256(packedData.readUint256(i + 20)));
      if (!_publish(appId, identifier, data)) {
        revert UnableToPublishData(packedData.readBytes(i, 52));
      }
    }
    return true;
  }

  // Dedicated function for price
  function publishPrice(bytes memory packedData) external onlyOperator returns (bool) {
    // Decode appId and chunksize
    bytes20 identifier;
    bytes32 data;
    if (packedData.length % 24 != 0) {
      revert InvalidDataLength(packedData.length);
    }
    for (uint256 i = 0; i < packedData.length; i += 24) {
      identifier = bytes20(bytes8(uint64(packedData.readUintUnsafe(i, 64))));
      data = bytes32(uint256(uint64(packedData.readUintUnsafe(i + 8, 128))));
      if (!_publish(1, identifier, data)) {
        revert UnableToPublishData(packedData.readBytes(i, 24));
      }
    }
    return true;
  }

  //=======================[  Interal  ]====================

  // Set deactivated status
  function _setDeactivateStatus(address userAddress, bool status) internal {
    deactivated[userAddress] = status;
    emit Deactivated(userAddress, status);
  }

  // Publish data to Orocle
  function _publish(uint32 appId, bytes20 identifier, bytes32 data) internal returns (bool) {
    (uint64 round, ) = _getMetadata(appId, identifier);
    round += 1;
    // After 255 round, we will reuse the same slot, it saving a lot of gas
    database[_encodeDataKey(appId, round, identifier)] = data;
    emit PublishData(appId, round, identifier, data);
    _setMetadata(appId, identifier, round);
    return true;
  }

  // Set application round
  function _setMetadata(uint32 appId, bytes20 identifier, uint64 round) internal {
    metadata[_encodeRoundKey(appId, identifier)] = _encodeMetadata(round, uint64(block.timestamp));
  }

  //=======================[  Interal View  ]====================

  // Encode data key
  function _encodeDataKey(uint32 appId, uint64 round, bytes20 identifier) internal pure returns (bytes32 dataKey) {
    assembly {
      dataKey := identifier
      dataKey := or(dataKey, shl(160, and(round, 0xff)))
      dataKey := or(dataKey, shl(224, appId))
    }
  }

  // Encode metadata
  function _encodeMetadata(uint64 round, uint64 lastUpdate) internal pure returns (bytes32 dataKey) {
    assembly {
      dataKey := shl(192, round)
      dataKey := or(dataKey, shl(128, lastUpdate))
    }
  }

  // Encode round key
  function _encodeRoundKey(uint32 appId, bytes20 identifier) internal pure returns (bytes32 roundKey) {
    assembly {
      roundKey := identifier
      roundKey := or(roundKey, shl(224, appId))
    }
  }

  // Decode metadata
  function _decodeMetadata(bytes32 metadataRecord) internal pure returns (uint64 round, uint64 lastUpdate) {
    assembly {
      round := shr(192, metadataRecord)
      lastUpdate := shr(128, metadataRecord)
    }
  }

  // Get application round
  function _getMetadata(uint32 appId, bytes20 identifier) internal view returns (uint64 round, uint64 lastUpdate) {
    return _decodeMetadata(metadata[_encodeRoundKey(appId, identifier)]);
  }

  /**
   * Publish data to database
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @param data Data
   */
  function _readDatabase(uint32 appId, uint64 round, bytes20 identifier) internal view returns (bytes32 data) {
    (uint64 onChainRound, ) = _getMetadata(appId, identifier);
    // Can't get > 255 round in the past
    if (round + 255 < onChainRound || round > onChainRound) {
      revert UndefinedRound(round);
    }
    return database[_encodeDataKey(appId, round, identifier)];
  }

  //=======================[  External View  ]====================

  // Check if user is deactivated
  function isDeactivated(address user) external view returns (bool) {
    return deactivated[user];
  }

  /**
   * Get round of a given application
   * @param appId Application ID
   * @return round
   */
  function getMetadata(uint32 appId, bytes20 identifier) external view returns (uint64 round, uint64 lastUpdate) {
    return _getMetadata(appId, identifier);
  }

  /**
   * Get data of an application
   * @param appId Application ID
   * @param round Round number
   * @param identifier Data identifier
   * @return data Data
   */
  function getData(uint32 appId, uint64 round, bytes20 identifier) external view onlyActive returns (bytes32 data) {
    return _readDatabase(appId, round, identifier);
  }

  /**
   * Get latest data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return data
   */
  function getLatestData(uint32 appId, bytes20 identifier) external view onlyActive returns (bytes32 data) {
    (uint64 round, ) = _getMetadata(appId, identifier);
    data = _readDatabase(appId, round, identifier);
  }

  /**
   * Get latest round and data of an application
   * @param appId Application ID
   * @param identifier Data identifier
   * @return round lastUpdate data
   */
  function getLatestRound(
    uint32 appId,
    bytes20 identifier
  ) external view onlyActive returns (uint64 round, uint64 lastUpdate, bytes32 data) {
    (round, lastUpdate) = _getMetadata(appId, identifier);
    data = _readDatabase(appId, round, identifier);
  }
}
