"""Schema packing only: no expected round calculation or upstream validation.

Key: [l_skip,n_stack,max_degree,N], then N 10-word records
[required,num_pv,need_rot,interactions,has_preprocessed,preprocessed_height,
 common_width,preprocessed_width,num_cached,cached_width_offset], then cached widths.
Proof: [trace_count,pv_count,numerators,denominators,univariate_coeffs,
 opening_count,batch_poly_count,gkr_claim_layers,gkr_poly_count], then N records
[present,log_height,cached_commitment_count,pv_count], followed by opening records
[air_id,part_count,*part_widths], then batch polynomial widths and GKR row lengths.
Opening air IDs are the adapter's association of the original ordered vectors
with present AIRs sorted by descending height, with AIR-ID tie order. PIR checks
that order, presence, counts and widths. No proof scalar/commitment is verified.
"""


def pack_openvm(row):
    k, p = row["key"], row["proof"]
    airs = k["airs"]
    key = [k["l_skip"], k["n_stack"], k["max_degree"], len(airs)]
    offset = 4 + 10 * len(airs)
    for a in airs:
        cached = a["cached_widths"]
        key += [int(a["required"]), a["public_values"], int(a["need_rot"]),
                a["interactions"], int(a["preprocessed_height"] is not None),
                a["preprocessed_height"] or 0, a["common_width"],
                a["preprocessed_width"] or 0, len(cached), offset]
        offset += len(cached)
    key += [w for a in airs for w in a["cached_widths"]]
    proof = [len(p["trace"]), len(p["public_values"]), p["numerators"], p["denominators"],
             p["univariate"], len(p["opening_widths"]), len(p["batch_widths"]),
             p["gkr_layers"], len(p["gkr_widths"])]
    for i, t in enumerate(p["trace"]):
        proof += [int(t is not None), t["log_height"] if t else 0,
                  t["cached_commitments"] if t else 0, p["public_values"][i]]
    # Preserve each actual width vector; never replace it with an expected width.
    order = sorted((i for i, t in enumerate(p["trace"]) if t is not None),
                   key=lambda i: (-p["trace"][i]["log_height"], i))
    for slot, widths in enumerate(p["opening_widths"]):
        proof += [order[slot] if slot < len(order) else len(airs), len(widths), *widths]
    return {"key": key, "proof": proof + p["batch_widths"] + p["gkr_widths"]}
