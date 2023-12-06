const fs = require('fs');
const bytes = fs.readFileSync('_demo/orig.wasm');
const val_1 = BigInt(0);
const val_2 = BigInt(1);

(async () => {
    const obj = await WebAssembly.instantiate(
        new Uint8Array (bytes), {}
    );
    console.log(`Calling function with inputs: ${val_1}, ${val_2}`);
    let resAlt = obj.instance.exports.hello(val_1, val_2);
    console.log(`===> ${resAlt}`);
})();
