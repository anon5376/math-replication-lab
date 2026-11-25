import test from 'node:test';
import assert from 'node:assert/strict';
import { result } from './cfh.mjs';

test('q=17: published coefficients and both exact discriminants', () => {
  const {h, f, D} = result(17n);
  assert.deepEqual(h, [1367432169863264385040621589n, 677031173160167651396287043n, 85823997163784007690567699n]);
  assert.deepEqual(f, [1367432169863264385040621589n, 677047053626088109460305403n, 85827739133054463066849240n]);
  assert.deepEqual(D, [-11062769241414341239970603495681493737981374532130995n,
                      -11061733404916469626152098526056073213151599377977031n]);
});
test('smaller prime powers in this construction have positive coefficients and discriminants', () => {
  for (const q of [2n,3n,4n,5n,7n,8n,9n,11n,13n,16n]) {
    const {h,f,D} = result(q);
    assert.ok([...h,...f,...D].every(x => x > 0n), `q=${q}`);
  }
});
