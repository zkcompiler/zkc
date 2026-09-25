// Protocol schedule using separately resolved implementation helpers.
module {
  dependency helpers = library(namespace="zkc.examples", name="air", version="1", resolution="source-v1");
  use helpers::{
    CommitBase,
    CommitExtension,
    OpenBase,
    OpenExtension,
    CheckBase,
    CheckExtension,
    Draw,
    Query,
    Prepare,
    Interleave,
    LiftVector,
    LiftScalar,
    LiftPolynomial,
    Auxiliary,
    Quotients,
    Equal,
    Evaluate,
    CheckOutOfDomain,
    Deep,
    DeepRow,
    Fold,
    Terminal,
    FoldPair,
    RowValue,
    Coordinates,
    EmptyStates,
    EmptyRoots,
    SaveState,
    SaveRoot,
    StateAt,
    RootAt,
    EmptyChallenges,
    SaveChallenge,
    ChallengeAt,
    NextIndex,
    QueryInit,
    QueryAppend,
    QueryAt,
    Parameters,
    HalfSize,
    DoubleSize,
    Square
  };
  protocol AirPermutation {
    roles (P, V);
    inputs (
      P left: Vector<koala-bear::Element>,
      P right: Vector<koala-bear::Element>,
      P sum_values: Vector<koala-bear::Element>,
      P p_initial: koala-bear::Element,
      P p_final_value: koala-bear::Element,
      P p_total: koala-bear::Element,
      V v_initial: koala-bear::Element,
      V v_final_value: koala-bear::Element,
      V v_total: koala-bear::Element,
      V coins: Rng<koala-bear.ext8-binomial3>
    );
    outputs (V bool);
    local P: let (p_n0, p_n1, p_n2, p_n8, p_n16, p_n32, p_shift) = Parameters();
    local P: let (p_e_initial) = LiftScalar(p_initial);
    local P: let (p_e_final_value) = LiftScalar(p_final_value);
    local P: let (p_e_total) = LiftScalar(p_total);
    local V: let (v_n0, v_n1, v_n2, v_n8, v_n16, v_n32, v_shift) = Parameters();
    local V: let (v_e_initial) = LiftScalar(v_initial);
    local V: let (v_e_final_value) = LiftScalar(v_final_value);
    local V: let (v_e_total) = LiftScalar(v_total);
    local P: let (left_poly, left_lde) = Prepare(left);
    local P: let (left_ext) = LiftVector(left_lde);
    local P: let (left_ext_poly) = LiftPolynomial(left_poly);
    local P: let (right_poly, right_lde) = Prepare(right);
    local P: let (right_ext) = LiftVector(right_lde);
    local P: let (right_ext_poly) = LiftPolynomial(right_poly);
    local P: let (sum_values_poly, sum_values_lde) = Prepare(sum_values);
    local P: let (sum_values_ext) = LiftVector(sum_values_lde);
    local P: let (sum_values_ext_poly) = LiftPolynomial(sum_values_poly);
    local P: let (right_rows) = Interleave(right_lde, sum_values_lde);
    local P: let (main_left_root, main_left_state) = CommitBase(left_lde, p_n1);
    message main_left_root: P(main_left_root) -> V(v_main_left_root);
    local P: let (main_right_root, main_right_state) = CommitBase(right_rows, p_n2);
    message main_right_root: P(main_right_root) -> V(v_main_right_root);
    local V: let (beta, coins_beta) = Draw(coins);
    message beta: V(beta) -> P(p_beta);
    local P: let (aux_left_poly, aux_left_lde, aux_left_terminal) = Auxiliary(left, p_beta);
    local P: let (aux_left_root, aux_left_state) = CommitExtension(aux_left_lde, p_n1);
    message aux_left_root: P(aux_left_root) -> V(v_aux_left_root);
    message aux_left_terminal: P(aux_left_terminal) -> V(v_aux_left_terminal);
    local P: let (aux_right_poly, aux_right_lde, aux_right_terminal) = Auxiliary(right, p_beta);
    local P: let (aux_right_root, aux_right_state) = CommitExtension(aux_right_lde, p_n1);
    message aux_right_root: P(aux_right_root) -> V(v_aux_right_root);
    message aux_right_terminal: P(aux_right_terminal) -> V(v_aux_right_terminal);
    local V: let (connection_valid) = Equal(v_aux_left_terminal, v_aux_right_terminal);
    local V: let (alpha, coins_alpha) = Draw(coins_beta);
    message alpha: V(alpha) -> P(p_alpha);
    local P: let (qleft_poly, qright_poly, qleft_lde, qright_lde, quotient_rows) = Quotients(
      left_ext,
      right_ext,
      sum_values_ext,
      aux_left_lde,
      aux_right_lde,
      p_beta,
      p_alpha,
      aux_left_terminal,
      aux_right_terminal,
      p_e_initial,
      p_e_final_value,
      p_e_total
    );
    local P: let (quotient_root, quotient_state) = CommitExtension(quotient_rows, p_n2);
    message quotient_root: P(quotient_root) -> V(v_quotient_root);
    local V: let (z, coins_z) = Draw(coins_alpha);
    message z: V(z) -> P(p_z);
    local P: let (left_ext_at_z, left_ext_at_next) = Evaluate(left_ext_poly, p_z);
    local P: let (right_ext_at_z, right_ext_at_next) = Evaluate(right_ext_poly, p_z);
    local P: let (sum_values_ext_at_z, sum_values_ext_at_next) = Evaluate(sum_values_ext_poly, p_z);
    local P: let (aux_left_at_z, aux_left_at_next) = Evaluate(aux_left_poly, p_z);
    local P: let (aux_right_at_z, aux_right_at_next) = Evaluate(aux_right_poly, p_z);
    local P: let (qleft_at_z, qleft_at_next) = Evaluate(qleft_poly, p_z);
    local P: let (qright_at_z, qright_at_next) = Evaluate(qright_poly, p_z);
    message left_ext_at_z: P(left_ext_at_z) -> V(v_left_ext_at_z);
    message right_ext_at_z: P(right_ext_at_z) -> V(v_right_ext_at_z);
    message sum_values_ext_at_z: P(sum_values_ext_at_z) -> V(v_sum_values_ext_at_z);
    message aux_left_at_z: P(aux_left_at_z) -> V(v_aux_left_at_z);
    message aux_right_at_z: P(aux_right_at_z) -> V(v_aux_right_at_z);
    message left_ext_at_next: P(left_ext_at_next) -> V(v_left_ext_at_next);
    message right_ext_at_next: P(right_ext_at_next) -> V(v_right_ext_at_next);
    message sum_values_ext_at_next: P(sum_values_ext_at_next) -> V(v_sum_values_ext_at_next);
    message aux_left_at_next: P(aux_left_at_next) -> V(v_aux_left_at_next);
    message aux_right_at_next: P(aux_right_at_next) -> V(v_aux_right_at_next);
    message qleft_at_z: P(qleft_at_z) -> V(v_qleft_at_z);
    message qright_at_z: P(qright_at_z) -> V(v_qright_at_z);
    local V: let (ood_valid) = CheckOutOfDomain(
      v_left_ext_at_z,
      v_right_ext_at_z,
      v_sum_values_ext_at_z,
      v_aux_left_at_z,
      v_aux_right_at_z,
      v_left_ext_at_next,
      v_right_ext_at_next,
      v_sum_values_ext_at_next,
      v_aux_left_at_next,
      v_aux_right_at_next,
      v_qleft_at_z,
      v_qright_at_z,
      beta,
      alpha,
      v_aux_left_terminal,
      v_aux_right_terminal,
      v_e_initial,
      v_e_final_value,
      v_e_total,
      z
    );
    local V: let (eta, coins_eta) = Draw(coins_z);
    message eta: V(eta) -> P(p_eta);
    local V: let (degree_mix, coins_degree_mix) = Draw(coins_eta);
    message degree_mix: V(degree_mix) -> P(p_degree_mix);
    local P: let (layer0) = Deep(
      left_ext,
      right_ext,
      sum_values_ext,
      aux_left_lde,
      aux_right_lde,
      qleft_lde,
      qright_lde,
      left_ext_at_z,
      right_ext_at_z,
      sum_values_ext_at_z,
      aux_left_at_z,
      aux_right_at_z,
      left_ext_at_next,
      right_ext_at_next,
      sum_values_ext_at_next,
      aux_left_at_next,
      aux_right_at_next,
      qleft_at_z,
      qright_at_z,
      p_z,
      p_eta,
      p_degree_mix
    );
    local P: let (p_empty_states) = EmptyStates();
    local V: let (v_empty_roots) = EmptyRoots();
    local V: let (v_empty_challenges) = EmptyChallenges();
    loop [fri_commitments] 3 carry (
      current = layer0,
      shift = p_shift,
      states = p_empty_states,
      roots = v_empty_roots,
      challenges = v_empty_challenges,
      random = coins_degree_mix
    ) capture (
      p_n1
    ) -> (fri_terminal_values, final_shift, fri_states, fri_roots, fri_challenges, after_fri) {
      local P: let (layer_root, layer_state) = CommitExtension(current, p_n1);
      message layer_root: P(layer_root) -> V(v_layer_root);
      local V: let (fold_challenge, coins_fold_challenge) = Draw(random);
      message fold_challenge: V(fold_challenge) -> P(p_fold_challenge);
      local P: let (folded, next_shift) = Fold(current, shift, p_fold_challenge);
      local P: let (next_states) = SaveState(states, layer_state);
      local V: let (next_roots) = SaveRoot(roots, v_layer_root);
      local V: let (next_challenges) = SaveChallenge(challenges, fold_challenge);
      yield (folded, next_shift, next_states, next_roots, next_challenges, coins_fold_challenge);
    }
    local P: let (terminal) = Terminal(fri_terminal_values);
    message terminal: P(terminal) -> V(v_terminal);
    local P: let (p_empty_queries, p_zero) = QueryInit();
    local V: let (v_empty_queries, v_zero) = QueryInit();
    loop [sample_queries] 3 carry (
      random = after_fri,
      p_queries = p_empty_queries,
      v_queries = v_empty_queries
    ) capture (v_n16) -> (after_queries, p_all_queries, v_all_queries) {
      local V: let (sampled_query, coins_sampled_query) = Query(random, v_n16);
      message sampled_query: V(sampled_query) -> P(p_sampled_query);
      local P: let (p_next_queries) = QueryAppend(p_queries, p_sampled_query);
      local V: let (v_next_queries) = QueryAppend(v_queries, sampled_query);
      yield (coins_sampled_query, p_next_queries, v_next_queries);
    }
    loop [answer_queries] 3 carry (p_position = p_zero, v_position = v_zero, accepted = ood_valid) capture (
      main_left_state,
      main_right_state,
      aux_left_state,
      aux_right_state,
      quotient_state,
      v_main_left_root,
      v_main_right_root,
      v_aux_left_root,
      v_aux_right_root,
      v_quotient_root,
      p_all_queries,
      v_all_queries,
      v_terminal,
      v_shift,
      z,
      eta,
      degree_mix,
      fri_states,
      fri_roots,
      fri_challenges,
      v_left_ext_at_z,
      v_right_ext_at_z,
      v_sum_values_ext_at_z,
      v_aux_left_at_z,
      v_aux_right_at_z,
      v_left_ext_at_next,
      v_right_ext_at_next,
      v_sum_values_ext_at_next,
      v_aux_left_at_next,
      v_aux_right_at_next,
      v_qleft_at_z,
      v_qright_at_z,
      p_n0,
      p_n1,
      p_n2,
      p_n8,
      p_n16,
      p_n32,
      v_n0,
      v_n1,
      v_n2,
      v_n8,
      v_n16,
      v_n32
    ) -> (p_final_position, v_final_position, accepted_all) {
      local P: let (p_query, p_next_position) = QueryAt(p_all_queries, p_position);
      local V: let (v_query, v_next_position) = QueryAt(v_all_queries, v_position);
      local P: let (query_p0, query_p1) = Coordinates(p_query, p_n32);
      local V: let (query_v0, query_v1) = Coordinates(v_query, v_n32);
      local P: let (query_main_left0_row, query_main_left0_path) = OpenBase(
        main_left_state,
        query_p0
      );
      message query_main_left0_row: P(query_main_left0_row) -> V(v_query_main_left0_row);
      message query_main_left0_path: P(query_main_left0_path) -> V(v_query_main_left0_path);
      local V: let (query_main_left0_authenticated) = CheckBase(
        v_main_left_root,
        v_n1,
        v_n32,
        query_v0,
        v_query_main_left0_row,
        v_query_main_left0_path
      );
      local V: let (query_main_left0_extension) = LiftVector(v_query_main_left0_row);
      local P: let (query_main_right0_row, query_main_right0_path) = OpenBase(
        main_right_state,
        query_p0
      );
      message query_main_right0_row: P(query_main_right0_row) -> V(v_query_main_right0_row);
      message query_main_right0_path: P(query_main_right0_path) -> V(v_query_main_right0_path);
      local V: let (query_main_right0_authenticated) = CheckBase(
        v_main_right_root,
        v_n2,
        v_n32,
        query_v0,
        v_query_main_right0_row,
        v_query_main_right0_path
      );
      local V: let (query_main_right0_extension) = LiftVector(v_query_main_right0_row);
      local P: let (query_aux_left0_row, query_aux_left0_path) = OpenExtension(
        aux_left_state,
        query_p0
      );
      message query_aux_left0_row: P(query_aux_left0_row) -> V(v_query_aux_left0_row);
      message query_aux_left0_path: P(query_aux_left0_path) -> V(v_query_aux_left0_path);
      local V: let (query_aux_left0_authenticated) = CheckExtension(
        v_aux_left_root,
        v_n1,
        v_n32,
        query_v0,
        v_query_aux_left0_row,
        v_query_aux_left0_path
      );
      local P: let (query_aux_right0_row, query_aux_right0_path) = OpenExtension(
        aux_right_state,
        query_p0
      );
      message query_aux_right0_row: P(query_aux_right0_row) -> V(v_query_aux_right0_row);
      message query_aux_right0_path: P(query_aux_right0_path) -> V(v_query_aux_right0_path);
      local V: let (query_aux_right0_authenticated) = CheckExtension(
        v_aux_right_root,
        v_n1,
        v_n32,
        query_v0,
        v_query_aux_right0_row,
        v_query_aux_right0_path
      );
      local P: let (query_quotient0_row, query_quotient0_path) = OpenExtension(
        quotient_state,
        query_p0
      );
      message query_quotient0_row: P(query_quotient0_row) -> V(v_query_quotient0_row);
      message query_quotient0_path: P(query_quotient0_path) -> V(v_query_quotient0_path);
      local V: let (query_quotient0_authenticated) = CheckExtension(
        v_quotient_root,
        v_n2,
        v_n32,
        query_v0,
        v_query_quotient0_row,
        v_query_quotient0_path
      );
      local V: let (query_deep0) = DeepRow(
        query_main_left0_extension,
        query_main_right0_extension,
        v_query_aux_left0_row,
        v_query_aux_right0_row,
        v_query_quotient0_row,
        v_left_ext_at_z,
        v_right_ext_at_z,
        v_sum_values_ext_at_z,
        v_aux_left_at_z,
        v_aux_right_at_z,
        v_left_ext_at_next,
        v_right_ext_at_next,
        v_sum_values_ext_at_next,
        v_aux_left_at_next,
        v_aux_right_at_next,
        v_qleft_at_z,
        v_qright_at_z,
        z,
        eta,
        degree_mix,
        query_v0
      );
      local P: let (query_main_left1_row, query_main_left1_path) = OpenBase(
        main_left_state,
        query_p1
      );
      message query_main_left1_row: P(query_main_left1_row) -> V(v_query_main_left1_row);
      message query_main_left1_path: P(query_main_left1_path) -> V(v_query_main_left1_path);
      local V: let (query_main_left1_authenticated) = CheckBase(
        v_main_left_root,
        v_n1,
        v_n32,
        query_v1,
        v_query_main_left1_row,
        v_query_main_left1_path
      );
      local V: let (query_main_left1_extension) = LiftVector(v_query_main_left1_row);
      local P: let (query_main_right1_row, query_main_right1_path) = OpenBase(
        main_right_state,
        query_p1
      );
      message query_main_right1_row: P(query_main_right1_row) -> V(v_query_main_right1_row);
      message query_main_right1_path: P(query_main_right1_path) -> V(v_query_main_right1_path);
      local V: let (query_main_right1_authenticated) = CheckBase(
        v_main_right_root,
        v_n2,
        v_n32,
        query_v1,
        v_query_main_right1_row,
        v_query_main_right1_path
      );
      local V: let (query_main_right1_extension) = LiftVector(v_query_main_right1_row);
      local P: let (query_aux_left1_row, query_aux_left1_path) = OpenExtension(
        aux_left_state,
        query_p1
      );
      message query_aux_left1_row: P(query_aux_left1_row) -> V(v_query_aux_left1_row);
      message query_aux_left1_path: P(query_aux_left1_path) -> V(v_query_aux_left1_path);
      local V: let (query_aux_left1_authenticated) = CheckExtension(
        v_aux_left_root,
        v_n1,
        v_n32,
        query_v1,
        v_query_aux_left1_row,
        v_query_aux_left1_path
      );
      local P: let (query_aux_right1_row, query_aux_right1_path) = OpenExtension(
        aux_right_state,
        query_p1
      );
      message query_aux_right1_row: P(query_aux_right1_row) -> V(v_query_aux_right1_row);
      message query_aux_right1_path: P(query_aux_right1_path) -> V(v_query_aux_right1_path);
      local V: let (query_aux_right1_authenticated) = CheckExtension(
        v_aux_right_root,
        v_n1,
        v_n32,
        query_v1,
        v_query_aux_right1_row,
        v_query_aux_right1_path
      );
      local P: let (query_quotient1_row, query_quotient1_path) = OpenExtension(
        quotient_state,
        query_p1
      );
      message query_quotient1_row: P(query_quotient1_row) -> V(v_query_quotient1_row);
      message query_quotient1_path: P(query_quotient1_path) -> V(v_query_quotient1_path);
      local V: let (query_quotient1_authenticated) = CheckExtension(
        v_quotient_root,
        v_n2,
        v_n32,
        query_v1,
        v_query_quotient1_row,
        v_query_quotient1_path
      );
      local V: let (query_deep1) = DeepRow(
        query_main_left1_extension,
        query_main_right1_extension,
        v_query_aux_left1_row,
        v_query_aux_right1_row,
        v_query_quotient1_row,
        v_left_ext_at_z,
        v_right_ext_at_z,
        v_sum_values_ext_at_z,
        v_aux_left_at_z,
        v_aux_right_at_z,
        v_left_ext_at_next,
        v_right_ext_at_next,
        v_sum_values_ext_at_next,
        v_aux_left_at_next,
        v_aux_right_at_next,
        v_qleft_at_z,
        v_qright_at_z,
        z,
        eta,
        degree_mix,
        query_v1
      );
      local P: let (p_first_half) = HalfSize(p_n32);
      local P: let (p_layer_size) = DoubleSize(p_first_half);
      local P: let (first_layer_state) = StateAt(fri_states, p_n0);
      local V: let (v_first_layer_root) = RootAt(fri_roots, v_n0);
      local V: let (first_layer_challenge) = ChallengeAt(fri_challenges, v_n0);
      local P: let (first_layer_p0, first_layer_p1) = Coordinates(p_query, p_layer_size);
      local V: let (first_layer_v0, first_layer_v1) = Coordinates(v_query, v_n32);
      local P: let (first_layer_0_row, first_layer_0_path) = OpenExtension(
        first_layer_state,
        first_layer_p0
      );
      message first_layer_0_row: P(first_layer_0_row) -> V(v_first_layer_0_row);
      message first_layer_0_path: P(first_layer_0_path) -> V(v_first_layer_0_path);
      local V: let (first_layer_0_authenticated) = CheckExtension(
        v_first_layer_root,
        v_n1,
        v_n32,
        first_layer_v0,
        v_first_layer_0_row,
        v_first_layer_0_path
      );
      local P: let (first_layer_1_row, first_layer_1_path) = OpenExtension(
        first_layer_state,
        first_layer_p1
      );
      message first_layer_1_row: P(first_layer_1_row) -> V(v_first_layer_1_row);
      message first_layer_1_path: P(first_layer_1_path) -> V(v_first_layer_1_path);
      local V: let (first_layer_1_authenticated) = CheckExtension(
        v_first_layer_root,
        v_n1,
        v_n32,
        first_layer_v1,
        v_first_layer_1_row,
        v_first_layer_1_path
      );
      local V: let (first_layer_expected, first_layer_selected, first_layer_half) = FoldPair(
        v_first_layer_0_row,
        v_first_layer_1_row,
        first_layer_challenge,
        v_shift,
        v_n32,
        first_layer_v0,
        v_query
      );
      local V: let (first_value0) = RowValue(v_first_layer_0_row);
      local V: let (first_valid0) = Equal(first_value0, query_deep0);
      local V: let (first_value1) = RowValue(v_first_layer_1_row);
      local V: let (first_valid1) = Equal(first_value1, query_deep1);
      local V: let (v_first_shift) = Square(v_shift);
      loop [fri_checks] 2 carry (
        p_index = first_layer_p0,
        v_index = first_layer_v0,
        p_round = p_n1,
        v_round = v_n1,
        p_size = p_first_half,
        v_size = first_layer_half,
        v_domain_shift = v_first_shift,
        expected = first_layer_expected
      ) capture (
        fri_states,
        fri_roots,
        fri_challenges,
        p_n1,
        v_n1
      ) -> (
        p_end_index,
        v_end_index,
        p_end_round,
        v_end_round,
        p_end_size,
        v_end_size,
        v_end_shift,
        expected_terminal
      ) {
        local P: let (p_half_size) = HalfSize(p_size);
        local P: let (p_layer_size) = DoubleSize(p_half_size);
        local P: let (next_layer_state) = StateAt(fri_states, p_round);
        local V: let (v_next_layer_root) = RootAt(fri_roots, v_round);
        local V: let (next_layer_challenge) = ChallengeAt(fri_challenges, v_round);
        local P: let (next_layer_p0, next_layer_p1) = Coordinates(p_index, p_layer_size);
        local V: let (next_layer_v0, next_layer_v1) = Coordinates(v_index, v_size);
        local P: let (next_layer_0_row, next_layer_0_path) = OpenExtension(
          next_layer_state,
          next_layer_p0
        );
        message next_layer_0_row: P(next_layer_0_row) -> V(v_next_layer_0_row);
        message next_layer_0_path: P(next_layer_0_path) -> V(v_next_layer_0_path);
        local V: let (next_layer_0_authenticated) = CheckExtension(
          v_next_layer_root,
          v_n1,
          v_size,
          next_layer_v0,
          v_next_layer_0_row,
          v_next_layer_0_path
        );
        local P: let (next_layer_1_row, next_layer_1_path) = OpenExtension(
          next_layer_state,
          next_layer_p1
        );
        message next_layer_1_row: P(next_layer_1_row) -> V(v_next_layer_1_row);
        message next_layer_1_path: P(next_layer_1_path) -> V(v_next_layer_1_path);
        local V: let (next_layer_1_authenticated) = CheckExtension(
          v_next_layer_root,
          v_n1,
          v_size,
          next_layer_v1,
          v_next_layer_1_row,
          v_next_layer_1_path
        );
        local V: let (next_layer_expected, next_layer_selected, next_layer_half) = FoldPair(
          v_next_layer_0_row,
          v_next_layer_1_row,
          next_layer_challenge,
          v_domain_shift,
          v_size,
          next_layer_v0,
          v_index
        );
        local V: let (fold_valid) = Equal(next_layer_selected, expected);
        local P: let (p_next_round) = NextIndex(p_round);
        local V: let (v_next_round) = NextIndex(v_round);
        local V: let (v_next_shift) = Square(v_domain_shift);
        yield (
          next_layer_p0,
          next_layer_v0,
          p_next_round,
          v_next_round,
          p_half_size,
          next_layer_half,
          v_next_shift,
          next_layer_expected
        );
      }
      local V: let (query_accepted) = Equal(expected_terminal, v_terminal);
      yield (p_next_position, v_next_position, query_accepted);
    }
    return (accepted_all);
  }

  instance concrete: AirPermutation {
    roles (P = P, V = V);
  }

  entry main = concrete;
}
