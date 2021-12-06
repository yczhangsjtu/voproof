///! This file is generated by https://github.com/yczhangsjtu/voproof-scripts/main.py
use super::*;

#[derive(Clone)]
pub struct HPRProverKey<E: PairingEngine> {
  pub verifier_key: HPRVerifierKey<E>,
  pub powers: Vec<E::G1Affine>,
  pub max_degree: u64,
  pub cap_m_mat: (Vec<u64>, Vec<u64>, Vec<E::Fr>),
  pub u_vec: Vec<E::Fr>,
  pub w_vec: Vec<E::Fr>,
  pub v_vec: Vec<E::Fr>,
  pub y_vec: Vec<E::Fr>,
}

#[derive(Clone)]
pub struct HPRVerifierKey<E: PairingEngine> {
  pub cm_u_vec: Commitment<E>,
  pub cm_w_vec: Commitment<E>,
  pub cm_v_vec: Commitment<E>,
  pub cm_y_vec: Commitment<E>,
  pub kzg_vk: VerifierKey<E>,
  pub size: HPRSize,
  pub degree_bound: u64,
}

#[derive(Clone)]
pub struct HPRProof<E: PairingEngine> {
  pub cm_w_vec_1: Commitment<E>,
  pub cm_s_vec: Commitment<E>,
  pub cm_h_vec: Commitment<E>,
  pub cm_r_vec_tilde: Commitment<E>,
  pub cm_t_vec: Commitment<E>,
  pub cm_h_vec_2: Commitment<E>,
  pub cm_h_vec_3: Commitment<E>,
  pub y: E::Fr,
  pub y_1: E::Fr,
  pub cap_w: KZGProof<E>,
  pub cap_w_1: KZGProof<E>,
}

pub struct VOProofHPR {}

impl<E: PairingEngine> SNARKProverKey<E> for HPRProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for HPRVerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for HPRProof<E> {}

impl VOProofHPR {
  pub fn get_max_degree(size: HPRSize) -> usize {
    (5 * size.ncols
      + 2 * size.adensity
      + 2 * size.bdensity
      + 2 * size.cdensity
      + 2 * size.ddensity
      + 2) as usize
  }
}

impl<E: PairingEngine> SNARK<E> for VOProofHPR {
  type Size = HPRSize;
  type CS = HPR<E::Fr>;
  type PK = HPRProverKey<E>;
  type VK = HPRVerifierKey<E>;
  type Ins = HPRInstance<E::Fr>;
  type Wit = HPRWitness<E::Fr>;
  type Pf = HPRProof<E>;

  fn setup(size: usize) -> Result<UniversalParams<E>, Error> {
    let rng = &mut test_rng();
    KZG10::<E, DensePoly<E::Fr>>::setup(size, rng)
  }

  fn index(
    pp: &UniversalParams<E>,
    cs: &HPR<E::Fr>,
  ) -> Result<(HPRProverKey<E>, HPRVerifierKey<E>), Error> {
    let max_degree = Self::get_max_degree(cs.get_size());
    let cap_d = pp.powers_of_g.len();
    assert!(cap_d > max_degree);

    let powers_of_g = pp.powers_of_g[..].to_vec();
    let size = cs.get_size();
    init_size!(cap_k, ncols, size);
    init_size!(cap_s_a, adensity, size);
    init_size!(cap_s_b, bdensity, size);
    init_size!(cap_s_c, cdensity, size);
    init_size!(cap_s_d, ddensity, size);
    concat_matrix_horizontally!(
      cap_m_mat, cap_k, cs.arows, cs.brows, cs.crows, cs.acols, cs.bcols, cs.ccols, cs.avals,
      cs.bvals, cs.cvals, cs.drows, cs.dvals
    );
    define_generator!(gamma, E);
    define_matrix_vectors!(u_vec, w_vec, v_vec, cap_m_mat, gamma);
    define_hadamard_vector!(y_vec, u_vec, w_vec);
    define_commit_vector!(
      cm_u_vec,
      u_vec,
      powers_of_g,
      cap_s_a + cap_s_b + cap_s_c + cap_s_d
    );
    define_commit_vector!(
      cm_w_vec,
      w_vec,
      powers_of_g,
      cap_s_a + cap_s_b + cap_s_c + cap_s_d
    );
    define_commit_vector!(
      cm_v_vec,
      v_vec,
      powers_of_g,
      cap_s_a + cap_s_b + cap_s_c + cap_s_d
    );
    define_commit_vector!(
      cm_y_vec,
      y_vec,
      powers_of_g,
      cap_s_a + cap_s_b + cap_s_c + cap_s_d
    );

    let verifier_key = HPRVerifierKey::<E> {
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
      HPRProverKey::<E> {
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
    define_vec!(w_vec, w.witness.0.clone());
    define_vec!(w_vec_1, w.witness.1.clone());
    define_vec!(w_vec_2, w.witness.2.clone());
    init_size!(cap_h, nrows, size);
    init_size!(cap_k, ncols, size);
    init_size!(cap_s_a, adensity, size);
    init_size!(cap_s_b, bdensity, size);
    init_size!(cap_s_c, cdensity, size);
    init_size!(cap_s_d, ddensity, size);
    define!(n, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1);
    define_concat_vector!(w_vec_1, w_vec, w_vec_1, w_vec_2);
    redefine_zero_pad_concat_vector!(w_vec_1, n, delta_vec);
    define_commit_vector!(cm_w_vec_1, w_vec_1, pk.powers, n + 1);
    define!(ell, cap_s_a + cap_s_b + cap_s_c + cap_s_d);
    define_generator!(gamma, E);
    get_randomness_from_hash!(
      mu,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_w_vec_1
    );
    define_expression_vector_inverse!(
      r_vec,
      i,
      minus!(mu, power_vector_index!(gamma, cap_h, i)),
      cap_h
    );
    define_left_sparse_mvp_vector!(c_vec, pk.cap_m_mat, r_vec, cap_h, 3 * cap_k + 1);
    define_concat_neg_vector!(s_vec, r_vec, c_vec);
    define_commit_vector!(cm_s_vec, s_vec, pk.powers, cap_h + 3 * cap_k + 1);
    get_randomness_from_hash!(
      nu,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_w_vec_1,
      cm_s_vec
    );
    define_expression_vector_inverse!(
      rnu_vec,
      i,
      minus!(nu, power_vector_index!(gamma, 3 * cap_k + 1, i)),
      3 * cap_k + 1
    );
    define_concat_uwinverse_vector!(h_vec, rnu_vec, mu, pk.u_vec, nu, pk.w_vec);
    define_commit_vector!(cm_h_vec, h_vec, pk.powers, 3 * cap_k + ell + 1);
    get_randomness_from_hash!(
      beta,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_w_vec_1,
      cm_s_vec,
      cm_h_vec
    );
    define_expression_vector!(
      r_vec_1,
      i,
      power_linear_combination!(
        beta,
        mul!(
          vector_index!(x_vec, minus_i64!(i, -cap_h - 3 * cap_k + n))
            + vector_index!(w_vec_1, minus_i64!(i, -3 * cap_k + n + 1))
            + delta!(i, -3 * cap_k + n),
          vector_index!(s_vec, minus_i64!(i, -cap_h - 3 * cap_k + n))
        ),
        minus!(
          mul!(
            -vector_index!(h_vec, minus_i64!(i, -3 * cap_k + n)),
            vector_index!(s_vec, minus_i64!(i, -cap_h - 3 * cap_k + n))
          ),
          mul!(
            vector_index!(h_vec, minus_i64!(i, -3 * cap_k - ell + n)),
            vector_index!(pk.v_vec, minus_i64!(i, -ell + n + 1))
          )
        )
      ),
      n
    );
    define_concat_vector!(r_vec_tilde, accumulate_vector_plus!(r_vec_1), delta_vec_1);
    define_commit_vector!(cm_r_vec_tilde, r_vec_tilde, pk.powers, n + 1);
    define!(
      maxshift,
      2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
    );
    get_randomness_from_hash!(
      alpha,
      one!(),
      x_vec,
      pk.verifier_key.cm_u_vec,
      pk.verifier_key.cm_w_vec,
      pk.verifier_key.cm_v_vec,
      pk.verifier_key.cm_y_vec,
      cm_w_vec_1,
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
    define!(c_9, power(alpha, 4));
    define!(c_10, -power(alpha, 4) * beta);
    define!(c_11, -power(alpha, 4));
    define_vec!(
      t_vec,
      vector_concat!(
        delta_vec_2,
        expression_vector!(
          i,
          c_1
            * range_index!(1, 3 * cap_k + 1, minus_i64!(i + n, 1))
            * range_index!(1, 3 * cap_k + 1, i + n)
            + c_10
              * vector_index!(s_vec, minus_i64!(i + n, -cap_h - 3 * cap_k + n))
              * vector_index!(h_vec, minus_i64!(i + n, -3 * cap_k + n))
            + c_10
              * vector_index!(h_vec, minus_i64!(i + n, -3 * cap_k - ell + n))
              * vector_index!(pk.v_vec, minus_i64!(i + n, -ell + n + 1))
            + c_11
              * range_index!(1, n, minus_i64!(i + n, 1))
              * (vector_index!(r_vec_tilde, minus_i64!(i + n, 1))
                - vector_index!(r_vec_tilde, minus_i64!(i + n, 2)))
            + c_2
              * vector_index!(h_vec, minus_i64!(i + n, 1))
              * (c_3 * vector_index!(pk.w_vec, minus_i64!(i + n, 3 * cap_k + 2))
                + c_4 * range_index!(1, ell, minus_i64!(i + n, 3 * cap_k + 2))
                + c_5 * vector_index!(pk.u_vec, minus_i64!(i + n, 3 * cap_k + 2))
                + vector_index!(pk.y_vec, minus_i64!(i + n, 3 * cap_k + 2)))
            + c_6 * power(range_index!(1, ell, minus_i64!(i + n, 3 * cap_k + 2)), 2)
            + c_7
              * vector_index!(w_vec_1, minus_i64!(i + n, -cap_k + n + 1))
              * vector_index!(w_vec_1, minus_i64!(i + n, -2 * cap_k + n + 1))
            + c_8
              * range_index!(1, cap_k, minus_i64!(i + n, -cap_k + n + 1))
              * vector_index!(w_vec_1, minus_i64!(i + n, -3 * cap_k + n + 1))
            + vector_index!(s_vec, minus_i64!(i + n, -cap_h - 3 * cap_k + n))
              * (power(alpha, 4) * delta!(i + n, -3 * cap_k + n)
                + c_9 * vector_index!(w_vec_1, minus_i64!(i + n, -3 * cap_k + n + 1))
                + c_9 * vector_index!(x_vec, minus_i64!(i + n, -cap_h - 3 * cap_k + n)))
            + vector_index!(h_vec, i + n)
              * (c * range_index!(1, 3 * cap_k + 1, minus_i64!(i + n, 1))
                + c_1 * power_vector_index!(gamma, 3 * cap_k + 1, minus_i64!(i + n, 1)))
            - range_index!(1, cap_h, minus_i64!(i + n, 1)) * range_index!(1, cap_h, i + n)
            + vector_index!(s_vec, i + n)
              * (mu * range_index!(1, cap_h, minus_i64!(i + n, 1))
                - power_vector_index!(gamma, cap_h, minus_i64!(i + n, 1))),
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
      cm_w_vec_1,
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
    define_vector_domain_evaluations_dict!(_w_vec_1_left_eval_dict, _w_vec_1_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_5,
      w_vec_1,
      w_vec_1,
      omega,
      shiftlength_4,
      _w_vec_1_left_eval_dict,
      _w_vec_1_right_eval_dict
    );
    define_vector_domain_evaluations_dict!(_x_vec_left_eval_dict, _x_vec_right_eval_dict);
    define_vector_domain_evaluations_dict!(_s_vec_left_eval_dict, _s_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_6,
      x_vec,
      s_vec,
      omega,
      shiftlength_5,
      _x_vec_left_eval_dict,
      _s_vec_right_eval_dict
    );
    define_vector_poly_mul_shift!(
      v_vec_7,
      w_vec_1,
      s_vec,
      omega,
      shiftlength_6,
      _w_vec_1_left_eval_dict,
      _s_vec_right_eval_dict
    );
    define_vector_poly_mul_shift!(
      v_vec_8,
      h_vec,
      s_vec,
      omega,
      shiftlength_7,
      _h_vec_left_eval_dict,
      _s_vec_right_eval_dict
    );
    define_vector_domain_evaluations_dict!(_pk_v_vec_left_eval_dict, _pk_v_vec_right_eval_dict);
    define_vector_poly_mul_shift!(
      v_vec_9,
      h_vec,
      pk.v_vec,
      omega,
      shiftlength_8,
      _h_vec_left_eval_dict,
      _pk_v_vec_right_eval_dict
    );
    define_vector_power_mul!(v_vec_10, s_vec, c_12, cap_h);
    define_vector_power_mul!(v_vec_11, s_vec, c_13, cap_h);
    define_vector_power_mul!(v_vec_12, h_vec, c_12, 3 * cap_k + 1);
    define_vector_power_mul!(v_vec_13, h_vec, c_13, 3 * cap_k + 1);
    define_vector_power_mul!(
      v_vec_14,
      v_vec_2,
      one!(),
      cap_s_a + cap_s_b + cap_s_c + cap_s_d
    );
    define_vector_power_mul!(v_vec_15, w_vec_1, c_12, cap_k);
    define_vector_power_mul!(
      v_vec_16,
      r_vec_tilde,
      c_12,
      3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
    );
    define_vector_power_mul!(
      v_vec_17,
      t_vec,
      c_12,
      2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 2
    );
    define_power_power_mul!(v_vec_18, c_12, cap_h, one!(), cap_h);
    define_power_power_mul!(v_vec_19, c_12, 3 * cap_k + 1, one!(), 3 * cap_k + 1);
    define_power_power_mul!(
      v_vec_20,
      c_12,
      cap_s_a + cap_s_b + cap_s_c + cap_s_d,
      one!(),
      cap_s_a + cap_s_b + cap_s_c + cap_s_d
    );
    define!(
      c_14,
      power(alpha, 4) * power(omega, cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(c_15, -power(alpha, 2) * mu);
    define!(c_16, -power(alpha, 2) * nu);
    define!(
      c_17,
      power(alpha, 3) * power(omega, 2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1)
    );
    define!(
      c_18,
      power(alpha, 4) * power(omega, -cap_h + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(
      c_19,
      power(alpha, 4) * power(omega, cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1)
    );
    define!(
      c_20,
      -power(alpha, 4) * beta * power(omega, cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(
      c_21,
      power(alpha, 5) * power(omega, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(c_22, mu * power(omega, cap_h - 1));
    define!(c_23, -power(gamma * omega, cap_h - 1));
    define!(c_24, alpha * nu * power(omega, 3 * cap_k));
    define!(c_25, -alpha * power(gamma * omega, 3 * cap_k));
    define!(c_26, power(alpha, 2) * mu * nu);
    define!(
      c_27,
      -power(alpha, 3) * power(omega, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(
      c_28,
      -power(alpha, 4) * power(omega, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(
      c_29,
      power(alpha, 4) * power(omega, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define!(
      c_30,
      -power(
        omega,
        5 * cap_k + 2 * cap_s_a + 2 * cap_s_b + 2 * cap_s_c + 2 * cap_s_d + 2
      )
    );
    define!(c_31, -power(omega, cap_h - 1));
    define!(c_32, -alpha * power(omega, 3 * cap_k));
    define!(
      c_33,
      -power(alpha, 2) * power(omega, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
    );
    define_expression_vector!(
      h_vec_2,
      i,
      c_10
        * vector_index!(
          v_vec_9,
          minus_i64!(i - maxshift - n, 3 * cap_k - shiftlength_8 + 2)
        )
        + c_14 * vector_index!(s_vec, minus_i64!(i - maxshift - n, 1 - cap_h))
        + c_15
          * vector_index!(
            v_vec_1,
            minus_i64!(i - maxshift - n, 3 * cap_k - shiftlength + 2)
          )
        + c_16
          * vector_index!(
            v_vec_3,
            minus_i64!(i - maxshift - n, 3 * cap_k - shiftlength_2 + 2)
          )
        + c_17
          * vector_index!(
            v_vec_5,
            minus_i64!(i - maxshift - n, -cap_k - shiftlength_4 + 1)
          )
        + c_18 * vector_index!(v_vec_6, minus_i64!(i - maxshift - n, 1 - shiftlength_5))
        + c_19
          * vector_index!(
            v_vec_7,
            minus_i64!(i - maxshift - n, -cap_h - shiftlength_6)
          )
        + c_2
          * vector_index!(
            v_vec_4,
            minus_i64!(i - maxshift - n, 3 * cap_k - shiftlength_3 + 2)
          )
        + c_20
          * vector_index!(
            v_vec_8,
            minus_i64!(i - maxshift - n, -cap_h - shiftlength_7 + 1)
          )
        + c_21 * vector_index!(r_vec_tilde, minus_i64!(i - maxshift - n, 2 - n))
        + c_22 * vector_index!(v_vec_10, minus_i64!(i - maxshift - n, 2 - cap_h))
        + c_23 * vector_index!(v_vec_11, minus_i64!(i - maxshift - n, 2 - cap_h))
        + c_24 * vector_index!(v_vec_12, minus_i64!(i - maxshift - n, 1 - 3 * cap_k))
        + c_25 * vector_index!(v_vec_13, minus_i64!(i - maxshift - n, 1 - 3 * cap_k))
        + c_26
          * vector_index!(
            v_vec_14,
            minus_i64!(i - maxshift - n, 3 * cap_k - shiftlength_1 + 2)
          )
        + c_27 * vector_index!(v_vec_15, minus_i64!(i - maxshift - n, 2 - 3 * cap_k))
        + c_28
          * vector_index!(
            v_vec_16,
            minus_i64!(
              i - maxshift - n,
              -3 * cap_k - cap_s_a - cap_s_b - cap_s_c - cap_s_d + 1
            )
          )
        + c_29
          * vector_index!(
            v_vec_16,
            minus_i64!(
              i - maxshift - n,
              -3 * cap_k - cap_s_a - cap_s_b - cap_s_c - cap_s_d + 2
            )
          )
        + c_30
          * vector_index!(
            v_vec_17,
            minus_i64!(
              i - maxshift - n,
              -2 * cap_k - cap_s_a - cap_s_b - cap_s_c - cap_s_d - 1
            )
          )
        + c_31 * vector_index!(v_vec_18, minus_i64!(i - maxshift - n, 2 - cap_h))
        + c_32 * vector_index!(v_vec_19, minus_i64!(i - maxshift - n, 1 - 3 * cap_k))
        + c_33
          * vector_index!(
            v_vec_20,
            minus_i64!(i - maxshift - n, -cap_s_a - cap_s_b - cap_s_c - cap_s_d + 2)
          ),
      maxshift + n
    );
    define_expression_vector!(
      h_vec_3,
      i,
      c_10 * vector_index!(v_vec_9, minus_i64!(i + 1, 3 * cap_k - shiftlength_8 + 2))
        + c_14 * vector_index!(s_vec, minus_i64!(i + 1, 1 - cap_h))
        + c_15 * vector_index!(v_vec_1, minus_i64!(i + 1, 3 * cap_k - shiftlength + 2))
        + c_16 * vector_index!(v_vec_3, minus_i64!(i + 1, 3 * cap_k - shiftlength_2 + 2))
        + c_17 * vector_index!(v_vec_5, minus_i64!(i + 1, -cap_k - shiftlength_4 + 1))
        + c_18 * vector_index!(v_vec_6, minus_i64!(i + 1, 1 - shiftlength_5))
        + c_19 * vector_index!(v_vec_7, minus_i64!(i + 1, -cap_h - shiftlength_6))
        + c_2 * vector_index!(v_vec_4, minus_i64!(i + 1, 3 * cap_k - shiftlength_3 + 2))
        + c_20 * vector_index!(v_vec_8, minus_i64!(i + 1, -cap_h - shiftlength_7 + 1))
        + c_21 * vector_index!(r_vec_tilde, minus_i64!(i + 1, 2 - n))
        + c_22 * vector_index!(v_vec_10, minus_i64!(i + 1, 2 - cap_h))
        + c_23 * vector_index!(v_vec_11, minus_i64!(i + 1, 2 - cap_h))
        + c_24 * vector_index!(v_vec_12, minus_i64!(i + 1, 1 - 3 * cap_k))
        + c_25 * vector_index!(v_vec_13, minus_i64!(i + 1, 1 - 3 * cap_k))
        + c_26 * vector_index!(v_vec_14, minus_i64!(i + 1, 3 * cap_k - shiftlength_1 + 2))
        + c_27 * vector_index!(v_vec_15, minus_i64!(i + 1, 2 - 3 * cap_k))
        + c_28
          * vector_index!(
            v_vec_16,
            minus_i64!(
              i + 1,
              -3 * cap_k - cap_s_a - cap_s_b - cap_s_c - cap_s_d + 1
            )
          )
        + c_29
          * vector_index!(
            v_vec_16,
            minus_i64!(
              i + 1,
              -3 * cap_k - cap_s_a - cap_s_b - cap_s_c - cap_s_d + 2
            )
          )
        + c_30
          * vector_index!(
            v_vec_17,
            minus_i64!(
              i + 1,
              -2 * cap_k - cap_s_a - cap_s_b - cap_s_c - cap_s_d - 1
            )
          )
        + c_31 * vector_index!(v_vec_18, minus_i64!(i + 1, 2 - cap_h))
        + c_32 * vector_index!(v_vec_19, minus_i64!(i + 1, 1 - 3 * cap_k))
        + c_33
          * vector_index!(
            v_vec_20,
            minus_i64!(i + 1, -cap_s_a - cap_s_b - cap_s_c - cap_s_d + 2)
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
      cm_w_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3
    );
    define_eval_vector_expression!(y, omega / z, i, vector_index!(h_vec, i), n + 1);
    define_eval_vector_expression!(y_1, omega / z, i, vector_index!(w_vec_1, i), n + 1);
    define!(y_2, eval_vector_as_poly!(x_vec, omega / z));
    define!(
      c_34,
      (power(alpha, 4)
        * power(z, -cap_h - 3 * cap_k + n - 1)
        * (omega - one!() * z)
        * (gamma * omega - one!() * z)
        * (-beta * y * power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d)
          + y_1 * power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1)
          + y_2 * power(omega / z, -cap_h + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
          + power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d))
        - z
          * (mu * (one!() - power(omega / z, cap_h)) * (gamma * omega - one!() * z)
            - (omega - one!() * z) * (one!() - power(gamma * omega / z, cap_h))))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(
      c_35,
      (power(alpha, 2)
        * (mu
          * nu
          * y
          * power(z, 3 * cap_k + 1)
          * (omega - one!() * z)
          * (one!() - power(z, ell))
          + power(z, 3 * cap_k + 2)
            * power(omega / z, 3 * cap_k + 1)
            * (one!() - power(z, ell))
            * (one!() - power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d)))
        + alpha
          * z
          * (one!() - power(z, 3 * cap_k + 1))
          * (one!() - power(omega / z, 3 * cap_k + 1))
        + z * (one!() - power(z, cap_h)) * (one!() - power(omega / z, cap_h)))
        / ((omega - one!() * z) * (one!() - z))
    );
    define!(
      c_36,
      -alpha
        * z
        * (nu * (one!() - power(omega / z, 3 * cap_k + 1)) * (gamma * omega - one!() * z)
          - (omega - one!() * z) * (one!() - power(gamma * omega / z, 3 * cap_k + 1)))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(c_37, -power(alpha, 2) * mu * y * power(z, 3 * cap_k + 1));
    define!(c_38, -power(alpha, 2) * nu * y * power(z, 3 * cap_k + 1));
    define!(c_39, power(alpha, 2) * y * power(z, 3 * cap_k + 1));
    define!(
      c_40,
      power(alpha, 3)
        * power(
          omega / z,
          2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
        )
        * (y_1 * power(z, -2 * cap_k + n) * (omega - one!() * z)
          + power(z, -3 * cap_k + n + 1) * (one!() - power(omega / z, cap_k)))
        / (omega - one!() * z)
    );
    define!(c_41, -power(alpha, 4) * beta * y * power(z, -ell + n));
    define!(
      c_42,
      power(alpha, 4)
        * (alpha
          * power(omega / z, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
          * (omega - one!() * z)
          - z
            * (-one!()
              + z
                * (one!()
                  - power(
                    omega / z,
                    3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
                  ))
              + power(
                omega / z,
                3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
              )))
        / (omega - one!() * z)
    );
    define!(
      c_43,
      power(z, n)
        * power(
          omega / z,
          3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
        )
        * (one!()
          - power(
            omega / z,
            2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 2
          ))
        / (omega - one!() * z)
    );
    define!(c_44, -power(z, -cap_d));
    define!(c_45, -z);
    define_vec_mut!(
      g_vec,
      expression_vector!(
        i,
        linear_combination_base_zero!(
          c_34,
          vector_index!(s_vec, i),
          c_36,
          vector_index!(h_vec, i),
          c_37,
          vector_index!(pk.w_vec, i),
          c_38,
          vector_index!(pk.u_vec, i),
          c_39,
          vector_index!(pk.y_vec, i),
          c_40,
          vector_index!(w_vec_1, i),
          c_41,
          vector_index!(pk.v_vec, i),
          c_42,
          vector_index!(r_vec_tilde, i),
          c_43,
          vector_index!(t_vec, i),
          c_44,
          vector_index!(h_vec_2, -cap_d + i + maxshift + n),
          c_45,
          vector_index!(h_vec_3, i)
        ),
        cap_d
      )
    );
    add_to_first_item!(g_vec, c_35);
    define_commitment_linear_combination!(
      cm_g,
      vk,
      c_35,
      cm_s_vec,
      c_34,
      cm_h_vec,
      c_36,
      vk.cm_w_vec,
      c_37,
      vk.cm_u_vec,
      c_38,
      vk.cm_y_vec,
      c_39,
      cm_w_vec_1,
      c_40,
      vk.cm_v_vec,
      c_41,
      cm_r_vec_tilde,
      c_42,
      cm_t_vec,
      c_43,
      cm_h_vec_2,
      c_44,
      cm_h_vec_3,
      c_45
    );
    define_poly_from_vec!(h_vec_poly, h_vec);
    define_poly_from_vec!(w_vec_1_poly, w_vec_1);
    define_poly_from_vec!(g_poly, g_vec);
    check_poly_eval!(g_poly, z, zero!(), "g does not evaluate to 0 at z");
    define!(fs, vec!(h_vec_poly, w_vec_1_poly));
    define!(gs, vec!(g_poly));
    get_randomness_from_hash!(
      rand_xi,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_w_vec_1,
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
      cm_w_vec_1,
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
      z
    );
    define!(z1, omega / z);
    define!(z2, z);

    let (cap_w, cap_w_1) = KZG10::batch_open(&pk.powers, &fs, &gs, &z1, &z2, &rand_xi, &rand_xi_2)?;
    Ok(HPRProof::<E> {
      cm_w_vec_1: cm_w_vec_1,
      cm_s_vec: cm_s_vec,
      cm_h_vec: cm_h_vec,
      cm_r_vec_tilde: cm_r_vec_tilde,
      cm_t_vec: cm_t_vec,
      cm_h_vec_2: cm_h_vec_2,
      cm_h_vec_3: cm_h_vec_3,
      y: y,
      y_1: y_1,
      cap_w: cap_w,
      cap_w_1: cap_w_1,
    })
  }
  fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
    let size = vk.size.clone();
    let cap_d = vk.degree_bound as i64;
    let rng = &mut test_rng();
    let cm_w_vec_1 = proof.cm_w_vec_1;
    let cm_s_vec = proof.cm_s_vec;
    let cm_h_vec = proof.cm_h_vec;
    let cm_r_vec_tilde = proof.cm_r_vec_tilde;
    let cm_t_vec = proof.cm_t_vec;
    let cm_h_vec_2 = proof.cm_h_vec_2;
    let cm_h_vec_3 = proof.cm_h_vec_3;
    let y = proof.y;
    let y_1 = proof.y_1;
    let cap_w = proof.cap_w;
    let cap_w_1 = proof.cap_w_1;
    define_vec!(x_vec, x.instance.clone());
    init_size!(cap_h, nrows, size);
    init_size!(cap_k, ncols, size);
    init_size!(cap_s_a, adensity, size);
    init_size!(cap_s_b, bdensity, size);
    init_size!(cap_s_c, cdensity, size);
    init_size!(cap_s_d, ddensity, size);
    define!(n, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1);
    define!(ell, cap_s_a + cap_s_b + cap_s_c + cap_s_d);
    define_generator!(gamma, E);
    get_randomness_from_hash!(
      mu,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_w_vec_1
    );
    get_randomness_from_hash!(
      nu,
      one!(),
      x_vec,
      vk.cm_u_vec,
      vk.cm_w_vec,
      vk.cm_v_vec,
      vk.cm_y_vec,
      cm_w_vec_1,
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
      cm_w_vec_1,
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
      cm_w_vec_1,
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
      cm_w_vec_1,
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
      cm_w_vec_1,
      cm_s_vec,
      cm_h_vec,
      cm_r_vec_tilde,
      cm_t_vec,
      cm_h_vec_2,
      cm_h_vec_3
    );
    define!(y_2, eval_vector_as_poly!(x_vec, omega / z));
    define!(
      c_34,
      (power(alpha, 4)
        * power(z, -cap_h - 3 * cap_k + n - 1)
        * (omega - one!() * z)
        * (gamma * omega - one!() * z)
        * (-beta * y * power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d)
          + y_1 * power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1)
          + y_2 * power(omega / z, -cap_h + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
          + power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d))
        - z
          * (mu * (one!() - power(omega / z, cap_h)) * (gamma * omega - one!() * z)
            - (omega - one!() * z) * (one!() - power(gamma * omega / z, cap_h))))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(
      c_35,
      (power(alpha, 2)
        * (mu
          * nu
          * y
          * power(z, 3 * cap_k + 1)
          * (omega - one!() * z)
          * (one!() - power(z, ell))
          + power(z, 3 * cap_k + 2)
            * power(omega / z, 3 * cap_k + 1)
            * (one!() - power(z, ell))
            * (one!() - power(omega / z, cap_s_a + cap_s_b + cap_s_c + cap_s_d)))
        + alpha
          * z
          * (one!() - power(z, 3 * cap_k + 1))
          * (one!() - power(omega / z, 3 * cap_k + 1))
        + z * (one!() - power(z, cap_h)) * (one!() - power(omega / z, cap_h)))
        / ((omega - one!() * z) * (one!() - z))
    );
    define!(
      c_36,
      -alpha
        * z
        * (nu * (one!() - power(omega / z, 3 * cap_k + 1)) * (gamma * omega - one!() * z)
          - (omega - one!() * z) * (one!() - power(gamma * omega / z, 3 * cap_k + 1)))
        / ((omega - one!() * z) * (gamma * omega - one!() * z))
    );
    define!(c_37, -power(alpha, 2) * mu * y * power(z, 3 * cap_k + 1));
    define!(c_38, -power(alpha, 2) * nu * y * power(z, 3 * cap_k + 1));
    define!(c_39, power(alpha, 2) * y * power(z, 3 * cap_k + 1));
    define!(
      c_40,
      power(alpha, 3)
        * power(
          omega / z,
          2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
        )
        * (y_1 * power(z, -2 * cap_k + n) * (omega - one!() * z)
          + power(z, -3 * cap_k + n + 1) * (one!() - power(omega / z, cap_k)))
        / (omega - one!() * z)
    );
    define!(c_41, -power(alpha, 4) * beta * y * power(z, -ell + n));
    define!(
      c_42,
      power(alpha, 4)
        * (alpha
          * power(omega / z, 3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d)
          * (omega - one!() * z)
          - z
            * (-one!()
              + z
                * (one!()
                  - power(
                    omega / z,
                    3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
                  ))
              + power(
                omega / z,
                3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
              )))
        / (omega - one!() * z)
    );
    define!(
      c_43,
      power(z, n)
        * power(
          omega / z,
          3 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 1
        )
        * (one!()
          - power(
            omega / z,
            2 * cap_k + cap_s_a + cap_s_b + cap_s_c + cap_s_d + 2
          ))
        / (omega - one!() * z)
    );
    define!(c_44, -power(z, -cap_d));
    define!(c_45, -z);
    define_commitment_linear_combination!(
      cm_g,
      vk,
      c_35,
      cm_s_vec,
      c_34,
      cm_h_vec,
      c_36,
      vk.cm_w_vec,
      c_37,
      vk.cm_u_vec,
      c_38,
      vk.cm_y_vec,
      c_39,
      cm_w_vec_1,
      c_40,
      vk.cm_v_vec,
      c_41,
      cm_r_vec_tilde,
      c_42,
      cm_t_vec,
      c_43,
      cm_h_vec_2,
      c_44,
      cm_h_vec_3,
      c_45
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
      cm_w_vec_1,
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
      cm_w_vec_1,
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
      z
    );
    define!(f_commitments, vec!(cm_h_vec, cm_w_vec_1));
    define!(g_commitments, vec!(cm_g));
    define!(f_values, vec!(y, y_1));
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
