#ifndef HMAC_SHA256_H_
#define HMAC_SHA256_H_

// Requirement TA2-REQ-60: Measurement algorithm
void hmac_sha256 (const uint8_t *key,size_t key_size,
                  const uint8_t *message,size_t message_size,
                  uint8_t *result);
/*$ spec hmac_sha256(pointer key, u64 key_size,
                     pointer message, u64 message_size,
                     pointer result);
  // @PropertyClass: P3-SOP
    requires
      take ki = each(u64 i; i >= 0u64 && i < key_size) {Owned<uint8_t>(array_shift<uint8_t>(key,i))};
      take mi = each(u64 i; i >= 0u64 && i < message_size) {Owned<uint8_t>(array_shift<uint8_t>(message,i))};
      take ri = each(u64 i; i >= 0u64 && i < 32u64) {Block<uint8_t>(array_shift<uint8_t>(result,i))};
    ensures
      take ko = each(u64 i; i >= 0u64 && i < key_size) {Owned<uint8_t>(array_shift<uint8_t>(key,i))};
      take mo = each(u64 i; i >= 0u64 && i < message_size) {Owned<uint8_t>(array_shift<uint8_t>(message,i))};
      take ro = each(u64 i; i >= 0u64 && i < 32u64) {Owned<uint8_t>(array_shift<uint8_t>(result,i))};
      ki==ko;
      mi==mo;
$*/

#endif // HMAC_SHA256_H_
