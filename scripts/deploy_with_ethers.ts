// This script can be used to deploy the "Storage" contract using ethers.js library.
// Please make sure to compile "./contracts/1_Storage.sol" file before running this script.
// And use Right click -> "Run" from context menu of the file to run the script. Shortcut: Ctrl+Shift+S

import { deploy } from './ethers-lib';
import { utils } from 'ethers'

  const OROCLE_OPERATOR = ['0x2dD7C57207FF0ded78fAF9220946143cEeFcE295','0x9c854357Db8aFE52CDfb74DF92Bb9462DdA8C2C3'];
  const ORAND_PUBLIC_KEY = '0451b73330cbf6af018c71cd21ed6c59a0e5f76c327e145463ed54239379c89033810a8d9b9452cbbcf48be9b4fe3ddcb62f17b172eeceb2a413e36d89c5531ad7';

const affineToNumberish = (affine: string): [string, string] => {
  const aff = affine.trim().replace(/^0x/gi, '').padStart(128, '0');
  return [`0x${aff.substring(0, 64)}`, `0x${aff.substring(64, 128)}`];
};

const publicKeyToNumberish = (pubkey: string): [string, string] => {
  const aff = pubkey.trim().replace(/^0x/gi, '').padStart(130, '0').substring(2, 130);
  return affineToNumberish(aff);
};

(async () => {
  try {
    const pk = ORAND_PUBLIC_KEY.replace(/^0x/gi, '').trim();
    const correspondingAddress = utils.getAddress(`0x${utils.keccak256(`0x${pk.substring(2, 130)}`).substring(26, 66)}`);
    const resultOrocle = await deploy('OrocleV1', [OROCLE_OPERATOR]);
    const resultECVRF = await deploy('OrandECVRFV2', []);
    const resultOrandV2 = await deploy('OrandProviderV2', [
      // Public key
      publicKeyToNumberish(pk),
      // Operator
      correspondingAddress,
      // ECVRF
      resultECVRF.address,
      // Orocle
      resultOrocle.address,
      // Batching
      200
    ]);
    console.log(
      `Corresponding address: ${correspondingAddress} , is valid publicKey?: ${correspondingAddress === (await resultOrandV2.getOperator())}`,
    );
    console.log(`Is Oracle deploy correct: ${resultOrocle.address === (await resultOrandV2.getOracle())}`);
    console.log(`Is VRF deploy correct: ${resultECVRF.address === (await resultOrandV2.getECVRFVerifier())}`);
    console.log(`Public key: ${resultOrandV2}`);
    console.log(`OrocleV1: ${resultOrocle.address}`);
    console.log(`OrandECVRFV2: ${resultECVRF.address}`);
    console.log(`OrandProviderV2: ${resultOrandV2.address}`);
  } catch (e) {
    console.log(e.message);
  }
})()