///! This file is generated by https://github.com/yczhangsjtu/voproof-scripts/main.py
use super::*;

#[derive(Clone)]
pub struct R1CSProverKey<E: PairingEngine> {
  pub verifier_key: R1CSVerifierKey<E>,
  pub powers: Vec<E::G1Affine>,
  pub max_degree: u64,
  pub cap_m_mat: (Vec<u64>, Vec<u64>, Vec<E::Fr>),
  pub u_vec: Vec<E::Fr>,
  pub w_vec: Vec<E::Fr>,
  pub v_vec: Vec<E::Fr>,
  pub y_vec: Vec<E::Fr>,
}

#[derive(Clone)]
pub struct R1CSVerifierKey<E: PairingEngine> {
  pub cm_u_vec: Commitment<E>,
  pub cm_w_vec: Commitment<E>,
  pub cm_v_vec: Commitment<E>,
  pub cm_y_vec: Commitment<E>,
  pub kzg_vk: VerifierKey<E>,
  pub size: R1CSSize,
  pub degree_bound: u64,
}

#[derive(Clone)]
pub struct R1CSProof<E: PairingEngine> {
  pub cm_u_vec_1: Commitment<E>,
  pub cm_s_vec: Commitment<E>,
  pub cm_h_vec: Commitment<E>,
  pub cm_r_vec_tilde: Commitment<E>,
  pub cm_t_vec: Commitment<E>,
  pub cm_h_vec_2: Commitment<E>,
  pub cm_h_vec_3: Commitment<E>,
  pub y: E::Fr,
  pub y_1: E::Fr,
  pub y_2: E::Fr,
  pub cap_w: KZGProof<E>,
  pub cap_w_1: KZGProof<E>,
}

pub struct VOProofR1CS {}

impl<E: PairingEngine> SNARKProverKey<E> for R1CSProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for R1CSVerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for R1CSProof<E> {}

impl VOProofR1CS {
  pub fn get_max_degree(size: R1CSSize) -> usize {
    (size.ncols + 2 * size.adensity + 2 * size.bdensity + 2 * size.cdensity) as usize
  }
}

impl<E: PairingEngine> SNARK<E> for VOProofR1CS {
  type Size = R1CSSize;
  type CS = R1CS<E::Fr>;
  type PK = R1CSProverKey<E>;
  type VK = R1CSVerifierKey<E>;
  type Ins = R1CSInstance<E::Fr>;
  type Wit = R1CSWitness<E::Fr>;
  type Pf = R1CSProof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error> {
    let rng = &mut test_rng();
    KZG10::<E, DensePoly<E::Fr>>::setup(size, rng)
  }

  fn index(
    pp: &UniversalParams<E>,
    cs: &R1CS<E::Fr>,
  ) -> Result<(R1CSProverKey<E>, R1CSVerifierKey<E>), Error> {
    let max_degree = Self::get_max_degree(cs.get_size());
    let cap_d = pp.powers_of_g.len();
    assert!(cap_d > max_degree);

    let powers_of_g = pp.powers_of_g[..].to_vec();
    let size = cs.get_size();
    init_size!(cap_h, nrows, size);
    init_size!(cap_s_a, adensity, size);
    init_size!(cap_s_b, bdensity, size);
    init_size!(cap_s_c, cdensity, size);
    concat_matrix_vertically!(
      cap_m_mat, cap_h, cs.arows, cs.brows, cs.crows, cs.acols, cs.bcols, cs.ccols, cs.avals,
      cs.bvals, cs.cvals
    );
    define_generator!(gamma, E);
    define_matrix_vectors!(u_vec, w_vec, v_vec, cap_m_mat, gamma);
    define_hadamard_vector!(y_vec, u_vec, w_vec);
    define_commit_vector!(cm_u_vec, u_vec, powers_of_g, cap_s_a + cap_s_b + cap_s_c);
    define_commit_vector!(cm_w_vec, w_vec, powers_of_g, cap_s_a + cap_s_b + cap_s_c);
    define_commit_vector!(cm_v_vec, v_vec, powers_of_g, cap_s_a + cap_s_b + cap_s_c);
    define_commit_vector!(cm_y_vec, y_vec, powers_of_g, cap_s_a + cap_s_b + cap_s_c);

    let verifier_key = R1CSVerifierKey::<E> {
      cm_u_vec: cm_u_vec,
      cm_w_vec: cm_w_vec,
      cm_v_vec: cm_v_vec,
      cm_y_vec: cm_y_vec,
      kzg_vk: VerifierKey {
        g: pp.powers_of_g[0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
      },
      size,
      degree_bound: cap_d as u64,
    };
    Ok((
      R1CSProverKey::<E> {
        verifier_key: verifier_key.clone(),
        powers: powers_of_g,
        max_degree: max_degree as u64,
        cap_m_mat: cap_m_mat,
        u_vec: u_vec,
        w_vec: w_vec,
        v_vec: v_vec,
        y_vec: y_vec,
      },
      verifier_key,
    ))
  }
  fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
    let size = pk.verifier_key.size.clone();
    let vk = pk.verifier_key.clone();
    let cap_d = pk.verifier_key.degree_bound as i64;
    let rng = &mut test_rng();
    sample_randomizers!(rng, delta_vec, 1, delta_vec_1, 1, delta_vec_2, 1);
    define_vec!(x_vec, x.instance.clone());
    define_vec!(w_vec, w.witness.clone());
    init_size!(cap_h, nrows, size);
    init_size!(cap_k, ncols, size);
    init_size!(cap_s_a, adensity, size);
    init_size!(cap_s_b, bdensity, size);
    init_size!(cap_s_c, cdensity, size);
    init_size!(ell, input_size, size);
    define!(n, cap_k + cap_s_a + cap_s_b + cap_s_c);
    define_sparse_mvp_concat_vector!(
      u_vec_1,
      pk.cap_m_mat,
      concat_and_one!(x_vec, w_vec),
      3 * cap_h,
      cap_k
    );
    redefine_zero_pad_concat_vector!(u_vec_1, n, delta_vec);
    define_commit_vector!(cm_u_vec_1, u_vec_1, pk.powers, n + 1);
    define!(ell_1, cap_s_a + cap_s_b + cap_s_c);
    define_generator!(gamma, E);
    get_randomness_from_hash!(
      mu,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_u_vec_1
    );
    define_expression_vector_inverse!(
      r_vec,
      i,
      minus!(mu, power_vector_index!(gamma, 3 * cap_h, i)),
      3 * cap_h
    );
    define_left_sparse_mvp_vector!(c_vec, pk.cap_m_mat, r_vec, 3 * cap_h, cap_k);
    define_concat_neg_vector!(s_vec, r_vec, c_vec);
    define_commit_vector!(cm_s_vec, s_vec, pk.powers, 3 * cap_h + cap_k);
    get_randomness_from_hash!(
      nu,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec
    );
    define_expression_vector_inverse!(
      rnu_vec,
      i,
      minus!(nu, power_vector_index!(gamma, cap_k, i)),
      cap_k
    );
    define_concat_uwinverse_vector!(h_vec, rnu_vec, mu, pk.u_vec, nu, pk.w_vec);
    define_commit_vector!(cm_h_vec, h_vec, pk.powers, cap_k + ell_1);
    get_randomness_from_hash!(
      beta,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec
    );
    define_expression_vector!(
      r_vec_1,
      i,
      power_linear_combination!(
        beta,
        mul!(
          vector_index!(u_vec_1, minus_i64!(i, -3 * cap_h - cap_k + n + 1)),
          vector_index!(s_vec, minus_i64!(i, -3 * cap_h - cap_k + n + 1))
        ),
        minus!(
          mul!(
            -vector_index!(h_vec, minus_i64!(i, -cap_k + n + 1)),
            vector_index!(s_vec, minus_i64!(i, -3 * cap_h - cap_k + n + 1))
          ),
          mul!(
            vector_index!(h_vec, minus_i64!(i, -cap_k - ell_1 + n + 1)),
            vector_index!(pk.v_vec, minus_i64!(i, -ell_1 + n + 1))
          )
        )
      ),
      n
    );
    define_concat_vector!(r_vec_tilde, accumulate_vector_plus!(r_vec_1), delta_vec_1);
    define_commit_vector!(cm_r_vec_tilde, r_vec_tilde, pk.powers, n + 1);
    define!(maxshift, cap_s_a + cap_s_b + cap_s_c);
    get_randomness_from_hash!(
      alpha,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde
    );
    define!(c, alpha * nu);
    define!(c_1, -alpha);
    define!(c_2, power(alpha, 2));
    define!(c_3, -mu);
    define!(c_4, mu * nu);
    define!(c_5, -nu);
    define!(c_6, -power(alpha, 2));
    define!(c_7, power(alpha, 3));
    define!(c_8, -power(alpha, 3));
    define!(c_9, power(alpha, 5));
    define!(c_10, -power(alpha, 5) * beta);
    define!(c_11, -power(alpha, 5));
    define_vec!(
      t_vec,
      vector_concat!(
        delta_vec_2,
        expression_vector!(
          i,
          c_1 * range_index!(1, cap_k, minus_i64!(i + n, 1)) * range_index!(1, cap_k, i + n)
            + c_10
              * vector_index!(s_vec, minus_i64!(i + n, -3 * cap_h - cap_k + n + 1))
              * vector_index!(h_vec, minus_i64!(i + n, -cap_k + n + 1))
            + c_10
              * vector_index!(h_vec, minus_i64!(i + n, -cap_k - ell_1 + n + 1))
              * vector_index!(pk.v_vec, minus_i64!(i + n, -ell_1 + n + 1))
            + c_2
              * vector_index!(h_vec, minus_i64!(i + n, 1))
              * (c_3 * vector_index!(pk.w_vec, minus_i64!(i + n, cap_k + 1))
                + c_4 * range_index!(1, ell_1, minus_i64!(i + n, cap_k + 1))
                + c_5 * vector_index!(pk.u_vec, minus_i64!(i + n, cap_k + 1))
                + vector_index!(pk.y_vec, minus_i64!(i + n, cap_k + 1)))
            + c_6 * power(range_index!(1, ell_1, minus_i64!(i + n, cap_k + 1)), 2)
            + c_7
              * vector_index!(u_vec_1, minus_i64!(i + n, -cap_h + n + 1))
              * vector_index!(u_vec_1, minus_i64!(i + n, -2 * cap_h + n + 1))
            + c_8
              * range_index!(1, cap_h, minus_i64!(i + n, -cap_h + n + 1))
              * vector_index!(u_vec_1, minus_i64!(i + n, -3 * cap_h + n + 1))
            + c_9
              * vector_index!(u_vec_1, minus_i64!(i + n, -3 * cap_h - cap_k + n + 1))
              * vector_index!(s_vec, minus_i64!(i + n, -3 * cap_h - cap_k + n + 1))
            + vector_index!(h_vec, i + n)
              * (c * range_index!(1, cap_k, minus_i64!(i + n, 1))
                + c_1 * power_vector_index!(gamma, cap_k, minus_i64!(i + n, 1)))
            - range_index!(1, 3 * cap_h, minus_i64!(i + n, 1)) * range_index!(1, 3 * cap_h, i + n)
            + vector_index!(s_vec, i + n)
              * (mu * range_index!(1, 3 * cap_h, minus_i64!(i + n, 1))
                - power_vector_index!(gamma, 3 * cap_h, minus_i64!(i + n, 1))),
          maxshift + 2
        )
      )
    );
    define_commit_vector!(cm_t_vec, t_vec, pk.powers, maxshift + 2);
    get_randomness_from_hash!(
      omega,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec
    );
    define!(c_12, omega.inverse().unwrap());
    define!(c_13, one!() / (gamma * omega));
    define_vector_domain_evaluations_dict!(_h_vec_left_eval_dict, _h_vec_right_eval_dict);
    define_vector_domain_evaluations_dict!(_pk_w_vec_left_eval_dict, _pk_w_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_1,
      h_vec,
      pk.w_vec,
      omega,
      shiftlength,
      _h_vec_left_eval_dict,
      _pk_w_vec_right_eval_dict
    );
    define_vector_reverse_omega_shift!(v_vec_2, h_vec, omega, shiftlength_1);
    define_vector_domain_evaluations_dict!(_pk_u_vec_left_eval_dict, _pk_u_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_3,
      h_vec,
      pk.u_vec,
      omega,
      shiftlength_2,
      _h_vec_left_eval_dict,
      _pk_u_vec_right_eval_dict
    );
    define_vector_domain_evaluations_dict!(_pk_y_vec_left_eval_dict, _pk_y_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_4,
      h_vec,
      pk.y_vec,
      omega,
      shiftlength_3,
      _h_vec_left_eval_dict,
      _pk_y_vec_right_eval_dict
    );
    define_vector_domain_evaluations_dict!(_u_vec_1_left_eval_dict, _u_vec_1_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_5,
      u_vec_1,
      u_vec_1,
      omega,
      shiftlength_4,
      _u_vec_1_left_eval_dict,
      _u_vec_1_right_eval_dict
    );
    define_vector_domain_evaluations_dict!(_s_vec_left_eval_dict, _s_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_6,
      u_vec_1,
      s_vec,
      omega,
      shiftlength_5,
      _u_vec_1_left_eval_dict,
      _s_vec_right_eval_dict
    );
    define_vector_poly_mul_shift!(
      v_vec_7,
      h_vec,
      s_vec,
      omega,
      shiftlength_6,
      _h_vec_left_eval_dict,
      _s_vec_right_eval_dict
    );
    define_vector_domain_evaluations_dict!(_pk_v_vec_left_eval_dict, _pk_v_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_8,
      h_vec,
      pk.v_vec,
      omega,
      shiftlength_7,
      _h_vec_left_eval_dict,
      _pk_v_vec_right_eval_dict
    );
    define_vector_reverse_omega_shift!(v_vec_9, r_vec_tilde, omega, shiftlength_8);
    define_vector_power_mul!(v_vec_10, s_vec, c_12, 3 * cap_h);
    define_vector_power_mul!(v_vec_11, s_vec, c_13, 3 * cap_h);
    define_vector_power_mul!(v_vec_12, h_vec, c_12, cap_k);
    define_vector_power_mul!(v_vec_13, h_vec, c_13, cap_k);
    define_vector_power_mul!(v_vec_14, v_vec_2, one!(), cap_s_a + cap_s_b + cap_s_c);
    define_vector_power_mul!(v_vec_15, u_vec_1, c_12, cap_h);
    define_vector_power_mul!(v_vec_16, u_vec_1, c_12, ell + 1);
    define_vector_power_mul!(v_vec_17, x_vec, c_12, ell + 1);
    define_vector_power_mul!(
      v_vec_18,
      v_vec_9,
      one!(),
      cap_k + cap_s_a + cap_s_b + cap_s_c
    );
    define_vector_power_mul!(v_vec_19, t_vec, c_12, cap_s_a + cap_s_b + cap_s_c + 1);
    define_power_power_mul!(v_vec_20, c_12, 3 * cap_h, one!(), 3 * cap_h);
    define_power_power_mul!(v_vec_21, c_12, cap_k, one!(), cap_k);
    define_power_power_mul!(
      v_vec_22,
      c_12,
      cap_s_a + cap_s_b + cap_s_c,
      one!(),
      cap_s_a + cap_s_b + cap_s_c
    );
    define!(c_14, -power(alpha, 2) * mu);
    define!(c_15, -power(alpha, 2) * nu);
    define!(
      c_16,
      power(alpha, 3) * power(omega, -cap_h + cap_k + cap_s_a + cap_s_b + cap_s_c)
    );
    define!(
      c_17,
      power(alpha, 5) * power(omega, -3 * cap_h + cap_s_a + cap_s_b + cap_s_c)
    );
    define!(
      c_18,
      -power(alpha, 5) * beta * power(omega, cap_s_a + cap_s_b + cap_s_c)
    );
    define!(c_19, power(alpha, 6));
    define!(c_20, -power(alpha, 4) * power(omega, 3 * cap_h + ell));
    define!(c_21, mu * power(omega, 3 * cap_h - 1));
    define!(c_22, -power(gamma * omega, 3 * cap_h - 1));
    define!(c_23, alpha * nu * power(omega, cap_k - 1));
    define!(c_24, -alpha * power(gamma * omega, cap_k - 1));
    define!(c_25, power(alpha, 2) * mu * nu);
    define!(
      c_26,
      -power(alpha, 3) * power(omega, cap_k + cap_s_a + cap_s_b + cap_s_c - 1)
    );
    define!(c_27, power(alpha, 4) * power(omega, 3 * cap_h + ell));
    define!(c_28, power(alpha, 5) * omega);
    define!(
      c_29,
      -power(omega, cap_k + 2 * cap_s_a + 2 * cap_s_b + 2 * cap_s_c)
    );
    define!(c_30, -power(omega, 3 * cap_h - 1));
    define!(c_31, -alpha * power(omega, cap_k - 1));
    define!(
      c_32,
      -power(alpha, 2) * power(omega, cap_k + cap_s_a + cap_s_b + cap_s_c - 1)
    );
    define_expression_vector!(
      h_vec_2,
      i,
      c_10
        * vector_index!(
          v_vec_8,
          minus_i64!(i - maxshift - n, cap_k - shiftlength_7 + 1)
        )
        + c_11 * vector_index!(v_vec_18, minus_i64!(i - maxshift - n, 1 - shiftlength_8))
        + c_14
          * vector_index!(
            v_vec_1,
            minus_i64!(i - maxshift - n, cap_k - shiftlength + 1)
          )
        + c_15
          * vector_index!(
            v_vec_3,
            minus_i64!(i - maxshift - n, cap_k - shiftlength_2 + 1)
          )
        + c_16
          * vector_index!(
            v_vec_5,
            minus_i64!(i - maxshift - n, -cap_h - shiftlength_4 + 1)
          )
        + c_17 * vector_index!(v_vec_6, minus_i64!(i - maxshift - n, 1 - shiftlength_5))
        + c_18
          * vector_index!(
            v_vec_7,
            minus_i64!(i - maxshift - n, -3 * cap_h - shiftlength_6 + 1)
          )
        + c_19 * vector_index!(v_vec_9, minus_i64!(i - maxshift - n, n - shiftlength_8))
        + c_2
          * vector_index!(
            v_vec_4,
            minus_i64!(i - maxshift - n, cap_k - shiftlength_3 + 1)
          )
        + c_20 * power_vector_index!(c_12, ell + 1, minus_i64!(i - maxshift - n, 1 - ell))
        + c_20 * vector_index!(v_vec_17, minus_i64!(i - maxshift - n, 2 - ell))
        + c_21 * vector_index!(v_vec_10, minus_i64!(i - maxshift - n, 2 - 3 * cap_h))
        + c_22 * vector_index!(v_vec_11, minus_i64!(i - maxshift - n, 2 - 3 * cap_h))
        + c_23 * vector_index!(v_vec_12, minus_i64!(i - maxshift - n, 2 - cap_k))
        + c_24 * vector_index!(v_vec_13, minus_i64!(i - maxshift - n, 2 - cap_k))
        + c_25
          * vector_index!(
            v_vec_14,
            minus_i64!(i - maxshift - n, cap_k - shiftlength_1 + 1)
          )
        + c_26 * vector_index!(v_vec_15, minus_i64!(i - maxshift - n, 2 - 3 * cap_h))
        + c_27 * vector_index!(v_vec_16, minus_i64!(i - maxshift - n, -3 * cap_h - ell + 1))
        + c_28 * vector_index!(v_vec_18, minus_i64!(i - maxshift - n, -shiftlength_8))
        + c_29
          * vector_index!(
            v_vec_19,
            minus_i64!(i - maxshift - n, -cap_s_a - cap_s_b - cap_s_c)
          )
        + c_30 * vector_index!(v_vec_20, minus_i64!(i - maxshift - n, 2 - 3 * cap_h))
        + c_31 * vector_index!(v_vec_21, minus_i64!(i - maxshift - n, 2 - cap_k))
        + c_32
          * vector_index!(
            v_vec_22,
            minus_i64!(i - maxshift - n, -cap_s_a - cap_s_b - cap_s_c + 2)
          ),
      maxshift + n
    );
    define_expression_vector!(
      h_vec_3,
      i,
      c_10 * vector_index!(v_vec_8, minus_i64!(i + 1, cap_k - shiftlength_7 + 1))
        + c_11 * vector_index!(v_vec_18, minus_i64!(i + 1, 1 - shiftlength_8))
        + c_14 * vector_index!(v_vec_1, minus_i64!(i + 1, cap_k - shiftlength + 1))
        + c_15 * vector_index!(v_vec_3, minus_i64!(i + 1, cap_k - shiftlength_2 + 1))
        + c_16 * vector_index!(v_vec_5, minus_i64!(i + 1, -cap_h - shiftlength_4 + 1))
        + c_17 * vector_index!(v_vec_6, minus_i64!(i + 1, 1 - shiftlength_5))
        + c_18 * vector_index!(v_vec_7, minus_i64!(i + 1, -3 * cap_h - shiftlength_6 + 1))
        + c_19 * vector_index!(v_vec_9, minus_i64!(i + 1, n - shiftlength_8))
        + c_2 * vector_index!(v_vec_4, minus_i64!(i + 1, cap_k - shiftlength_3 + 1))
        + c_20 * power_vector_index!(c_12, ell + 1, minus_i64!(i + 1, 1 - ell))
        + c_20 * vector_index!(v_vec_17, minus_i64!(i + 1, 2 - ell))
        + c_21 * vector_index!(v_vec_10, minus_i64!(i + 1, 2 - 3 * cap_h))
        + c_22 * vector_index!(v_vec_11, minus_i64!(i + 1, 2 - 3 * cap_h))
        + c_23 * vector_index!(v_vec_12, minus_i64!(i + 1, 2 - cap_k))
        + c_24 * vector_index!(v_vec_13, minus_i64!(i + 1, 2 - cap_k))
        + c_25 * vector_index!(v_vec_14, minus_i64!(i + 1, cap_k - shiftlength_1 + 1))
        + c_26 * vector_index!(v_vec_15, minus_i64!(i + 1, 2 - 3 * cap_h))
        + c_27 * vector_index!(v_vec_16, minus_i64!(i + 1, -3 * cap_h - ell + 1))
        + c_28 * vector_index!(v_vec_18, minus_i64!(i + 1, -shiftlength_8))
        + c_29 * vector_index!(v_vec_19, minus_i64!(i + 1, -cap_s_a - cap_s_b - cap_s_c))
        + c_30 * vector_index!(v_vec_20, minus_i64!(i + 1, 2 - 3 * cap_h))
        + c_31 * vector_index!(v_vec_21, minus_i64!(i + 1, 2 - cap_k))
        + c_32
          * vector_index!(
            v_vec_22,
            minus_i64!(i + 1, -cap_s_a - cap_s_b - cap_s_c + 2)
          ),
      maxshift + n
    );
    define_commit_vector!(cm_h_vec_2, h_vec_2, pk.powers, cap_d);
    define_commit_vector!(cm_h_vec_3, h_vec_3, pk.powers, maxshift + n);
    get_randomness_from_hash!(
      z,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3
    );
    define_eval_vector_expression!(y, omega / z, i, vector_index!(h_vec, i), n + 1);
    define_eval_vector_expression!(y_1, omega / z, i, vector_index!(u_vec_1, i), n + 1);
    define_eval_vector_expression!(y_2, omega / z, i, vector_index!(r_vec_tilde, i), n + 1);
    define!(
      c_33,
      (power(alpha, 5)
        * power(z, -3 * cap_h - cap_k + n)
        * (omega - one!() * z)
        * (gamma * omega - one!() * z)
        * (-beta * y * power(omega / z, cap_s_a + cap_s_b + cap_s_c)
          + y_1 * power(omega / z, -3 * cap_h + cap_s_a + cap_s_b + cap_s_c))
        - z
          * (mu * (one!() - power(omega / z, 3 * cap_h)) * (gamma * omega - one!() * z)
            - (omega - one!() * z) * (one!() - power(gamma * omega / z, 3 * cap_h))))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(
      c_34,
      (power(alpha, 6) * y_2 * power(z, n) * (omega - one!() * z) * (one!() - z)
        + power(alpha, 5) * y_2 * (omega - z) * (omega - one!() * z) * (one!() - power(z, n))
        + power(alpha, 4)
          * z
          * power(omega / z, 3 * cap_h)
          * (one!() - z)
          * (-eval_vector_expression!(z, i, vector_index!(x_vec, i), ell)
            * power(z, 3 * cap_h + 1)
            * (omega * power(omega / z, ell) - one!() * z)
            + power(z, 3 * cap_h) * (-omega * power(omega / z, ell) + one!() * z))
        + power(alpha, 2)
          * mu
          * nu
          * y
          * power(z, cap_k + 1)
          * (omega - one!() * z)
          * (one!() - power(z, ell_1))
        + z
          * (power(alpha, 2)
            * power(z, cap_k + 1)
            * power(omega / z, cap_k)
            * (one!() - power(z, ell_1))
            * (one!() - power(omega / z, cap_s_a + cap_s_b + cap_s_c))
            + alpha * z * (one!() - power(z, cap_k)) * (one!() - power(omega / z, cap_k))
            + z * (one!() - power(z, 3 * cap_h)) * (one!() - power(omega / z, 3 * cap_h))))
        / (z * (omega - one!() * z) * (one!() - z))
    );
    define!(
      c_35,
      -alpha
        * z
        * (nu * (one!() - power(omega / z, cap_k)) * (gamma * omega - one!() * z)
          - (omega - one!() * z) * (one!() - power(gamma * omega / z, cap_k)))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(c_36, -power(alpha, 2) * mu * y * power(z, cap_k));
    define!(c_37, -power(alpha, 2) * nu * y * power(z, cap_k));
    define!(c_38, power(alpha, 2) * y * power(z, cap_k));
    define!(
      c_39,
      power(alpha, 3)
        * (alpha * power(omega / z, 3 * cap_h) * (omega * power(omega / z, ell) - one!() * z)
          + y_1
            * power(z, -2 * cap_h + n)
            * power(omega / z, -cap_h + cap_k + cap_s_a + cap_s_b + cap_s_c)
            * (omega - one!() * z)
          + power(z, -3 * cap_h + n + 1)
            * power(omega / z, -cap_h + cap_k + cap_s_a + cap_s_b + cap_s_c)
            * (one!() - power(omega / z, cap_h)))
        / (omega - one!() * z)
    );
    define!(c_40, -power(alpha, 5) * beta * y * power(z, -ell_1 + n));
    define!(
      c_41,
      power(z, n)
        * power(omega / z, cap_k + cap_s_a + cap_s_b + cap_s_c)
        * (one!() - power(omega / z, cap_s_a + cap_s_b + cap_s_c + 1))
        / (omega - one!() * z)
    );
    define!(c_42, -power(z, -cap_d));
    define!(c_43, -z);
    define_vec_mut!(
      g_vec,
      expression_vector!(
        i,
        linear_combination_base_zero!(
          c_33,
          vector_index!(s_vec, i),
          c_35,
          vector_index!(h_vec, i),
          c_36,
          vector_index!(pk.w_vec, i),
          c_37,
          vector_index!(pk.u_vec, i),
          c_38,
          vector_index!(pk.y_vec, i),
          c_39,
          vector_index!(u_vec_1, i),
          c_40,
          vector_index!(pk.v_vec, i),
          c_41,
          vector_index!(t_vec, i),
          c_42,
          vector_index!(h_vec_2, -cap_d + i + maxshift + n),
          c_43,
          vector_index!(h_vec_3, i)
        ),
        cap_d
      )
    );
    add_to_first_item!(g_vec, c_34);
    define_commitment_linear_combination!(
      cm_g,
      vk,
      c_34,
      cm_s_vec,
      c_33,
      cm_h_vec,
      c_35,
      vk.cm_w_vec,
      c_36,
      vk.cm_u_vec,
      c_37,
      vk.cm_y_vec,
      c_38,
      cm_u_vec_1,
      c_39,
      vk.cm_v_vec,
      c_40,
      cm_t_vec,
      c_41,
      cm_h_vec_2,
      c_42,
      cm_h_vec_3,
      c_43
    );
    define_poly_from_vec!(h_vec_poly, h_vec);
    define_poly_from_vec!(u_vec_1_poly, u_vec_1);
    define_poly_from_vec!(r_vec_tilde_poly, r_vec_tilde);
    define_poly_from_vec!(g_poly, g_vec);
    check_poly_eval!(g_poly, z, zero!(), "g does not evaluate to 0 at z");
    define!(fs, vec!(h_vec_poly, u_vec_1_poly, r_vec_tilde_poly));
    define!(gs, vec!(g_poly));
    get_randomness_from_hash!(
      rand_xi,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3,
      cm_g,
      omega / z,
      y,
      y_1,
      y_2,
      z
    );
    get_randomness_from_hash!(
      rand_xi_2,
      scalar_to_field!(2),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3,
      cm_g,
      omega / z,
      y,
      y_1,
      y_2,
      z
    );
    define!(z1, omega / z);
    define!(z2, z);

    let (cap_w, cap_w_1) = KZG10::batch_open(&pk.powers, &fs, &gs, &z1, &z2, &rand_xi, &rand_xi_2)?;
    Ok(R1CSProof::<E> {
      cm_u_vec_1: cm_u_vec_1,
      cm_s_vec: cm_s_vec,
      cm_h_vec: cm_h_vec,
      cm_r_vec_tilde: cm_r_vec_tilde,
      cm_t_vec: cm_t_vec,
      cm_h_vec_2: cm_h_vec_2,
      cm_h_vec_3: cm_h_vec_3,
      y: y,
      y_1: y_1,
      y_2: y_2,
      cap_w: cap_w,
      cap_w_1: cap_w_1,
    })
  }
  fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
    let size = vk.size.clone();
    let cap_d = vk.degree_bound as i64;
    let rng = &mut test_rng();
    let cm_u_vec_1 = proof.cm_u_vec_1;
    let cm_s_vec = proof.cm_s_vec;
    let cm_h_vec = proof.cm_h_vec;
    let cm_r_vec_tilde = proof.cm_r_vec_tilde;
    let cm_t_vec = proof.cm_t_vec;
    let cm_h_vec_2 = proof.cm_h_vec_2;
    let cm_h_vec_3 = proof.cm_h_vec_3;
    let y = proof.y;
    let y_1 = proof.y_1;
    let y_2 = proof.y_2;
    let cap_w = proof.cap_w;
    let cap_w_1 = proof.cap_w_1;
    define_vec!(x_vec, x.instance.clone());
    init_size!(cap_h, nrows, size);
    init_size!(cap_k, ncols, size);
    init_size!(cap_s_a, adensity, size);
    init_size!(cap_s_b, bdensity, size);
    init_size!(cap_s_c, cdensity, size);
    init_size!(ell, input_size, size);
    define!(n, cap_k + cap_s_a + cap_s_b + cap_s_c);
    define!(ell_1, cap_s_a + cap_s_b + cap_s_c);
    define_generator!(gamma, E);
    get_randomness_from_hash!(
      mu,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1
    );
    get_randomness_from_hash!(
      nu,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec
    );
    get_randomness_from_hash!(
      beta,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec
    );
    get_randomness_from_hash!(
      alpha,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde
    );
    get_randomness_from_hash!(
      omega,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec
    );
    get_randomness_from_hash!(
      z,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3
    );
    define!(
      c_33,
      (power(alpha, 5)
        * power(z, -3 * cap_h - cap_k + n)
        * (omega - one!() * z)
        * (gamma * omega - one!() * z)
        * (-beta * y * power(omega / z, cap_s_a + cap_s_b + cap_s_c)
          + y_1 * power(omega / z, -3 * cap_h + cap_s_a + cap_s_b + cap_s_c))
        - z
          * (mu * (one!() - power(omega / z, 3 * cap_h)) * (gamma * omega - one!() * z)
            - (omega - one!() * z) * (one!() - power(gamma * omega / z, 3 * cap_h))))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(
      c_34,
      (power(alpha, 6) * y_2 * power(z, n) * (omega - one!() * z) * (one!() - z)
        + power(alpha, 5) * y_2 * (omega - z) * (omega - one!() * z) * (one!() - power(z, n))
        + power(alpha, 4)
          * z
          * power(omega / z, 3 * cap_h)
          * (one!() - z)
          * (-eval_vector_expression!(z, i, vector_index!(x_vec, i), ell)
            * power(z, 3 * cap_h + 1)
            * (omega * power(omega / z, ell) - one!() * z)
            + power(z, 3 * cap_h) * (-omega * power(omega / z, ell) + one!() * z))
        + power(alpha, 2)
          * mu
          * nu
          * y
          * power(z, cap_k + 1)
          * (omega - one!() * z)
          * (one!() - power(z, ell_1))
        + z
          * (power(alpha, 2)
            * power(z, cap_k + 1)
            * power(omega / z, cap_k)
            * (one!() - power(z, ell_1))
            * (one!() - power(omega / z, cap_s_a + cap_s_b + cap_s_c))
            + alpha * z * (one!() - power(z, cap_k)) * (one!() - power(omega / z, cap_k))
            + z * (one!() - power(z, 3 * cap_h)) * (one!() - power(omega / z, 3 * cap_h))))
        / (z * (omega - one!() * z) * (one!() - z))
    );
    define!(
      c_35,
      -alpha
        * z
        * (nu * (one!() - power(omega / z, cap_k)) * (gamma * omega - one!() * z)
          - (omega - one!() * z) * (one!() - power(gamma * omega / z, cap_k)))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(c_36, -power(alpha, 2) * mu * y * power(z, cap_k));
    define!(c_37, -power(alpha, 2) * nu * y * power(z, cap_k));
    define!(c_38, power(alpha, 2) * y * power(z, cap_k));
    define!(
      c_39,
      power(alpha, 3)
        * (alpha * power(omega / z, 3 * cap_h) * (omega * power(omega / z, ell) - one!() * z)
          + y_1
            * power(z, -2 * cap_h + n)
            * power(omega / z, -cap_h + cap_k + cap_s_a + cap_s_b + cap_s_c)
            * (omega - one!() * z)
          + power(z, -3 * cap_h + n + 1)
            * power(omega / z, -cap_h + cap_k + cap_s_a + cap_s_b + cap_s_c)
            * (one!() - power(omega / z, cap_h)))
        / (omega - one!() * z)
    );
    define!(c_40, -power(alpha, 5) * beta * y * power(z, -ell_1 + n));
    define!(
      c_41,
      power(z, n)
        * power(omega / z, cap_k + cap_s_a + cap_s_b + cap_s_c)
        * (one!() - power(omega / z, cap_s_a + cap_s_b + cap_s_c + 1))
        / (omega - one!() * z)
    );
    define!(c_42, -power(z, -cap_d));
    define!(c_43, -z);
    define_commitment_linear_combination!(
      cm_g,
      vk,
      c_34,
      cm_s_vec,
      c_33,
      cm_h_vec,
      c_35,
      vk.cm_w_vec,
      c_36,
      vk.cm_u_vec,
      c_37,
      vk.cm_y_vec,
      c_38,
      cm_u_vec_1,
      c_39,
      vk.cm_v_vec,
      c_40,
      cm_t_vec,
      c_41,
      cm_h_vec_2,
      c_42,
      cm_h_vec_3,
      c_43
    );
    define!(z1, omega / z);
    define!(z2, z);
    get_randomness_from_hash!(
      rand_xi,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3,
      cm_g,
      omega / z,
      y,
      y_1,
      y_2,
      z
    );
    get_randomness_from_hash!(
      rand_xi_2,
      scalar_to_field!(2),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_u_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3,
      cm_g,
      omega / z,
      y,
      y_1,
      y_2,
      z
    );
    define!(f_commitments, vec!(cm_h_vec, cm_u_vec_1, cm_r_vec_tilde));
    define!(g_commitments, vec!(cm_g));
    define!(f_values, vec!(y, y_1, y_2));
    define!(g_values, vec!(zero!()));

    if KZG10::<E, DensePoly<E::Fr>>::batch_check(
      &vk.kzg_vk,
      &f_commitments,
      &g_commitments,
      &z1,
      &z2,
      &rand_xi,
      &rand_xi_2,
      &f_values,
      &g_values,
      &cap_w,
      &cap_w_1,
      rng,
    )? {
      Ok(())
    } else {
      Err(Error::VerificationFail)
    }
  }
}
