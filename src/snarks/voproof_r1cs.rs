///! This file is generated by scripts/main.py
use super::*;

#[derive(Clone)]
pub struct R1CSProverKey<E: PairingEngine> {
    pub verifier_key: R1CSVerifierKey<E>,
    pub powers: Vec<E::G1Affine>,
    pub max_degree: u64,
    pub M_mat: (Vec<u64>, Vec<u64>, Vec<E::Fr>),
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
    pub D: u64,
}

#[derive(Clone)]
pub struct R1CSProof<E: PairingEngine> {
    pub cm_u_vec_1: Commitment<E>,
    pub cm_s_vec: Commitment<E>,
    pub cm_h_vec: Commitment<E>,
    pub cm_r_vec_tilde: Commitment<E>,
    pub cm_t_vec_1: Commitment<E>,
    pub cm_h_vec_2: Commitment<E>,
    pub cm_h_vec_3: Commitment<E>,
    pub y: E::Fr,
    pub y_1: E::Fr,
    pub y_2: E::Fr,
    pub W: KZGProof<E>,
    pub W_1: KZGProof<E>,
}

pub struct VOProofR1CS {}

impl<E: PairingEngine> SNARKProverKey<E> for R1CSProverKey<E> {}

impl<E: PairingEngine> SNARKVerifierKey<E> for R1CSVerifierKey<E> {}

impl<E: PairingEngine> SNARKProof<E> for R1CSProof<E> {}

impl VOProofR1CS {
    pub fn get_max_degree(size: R1CSSize) -> usize {
        let H=size.nrows as i64;
        let K=size.ncols as i64;
        let S=size.density as i64;
        let ell=size.input_size as i64;
        
        (K + 6*S) as usize
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

    fn index(pp: &UniversalParams<E>, cs: &R1CS<E::Fr>)
        -> Result<(R1CSProverKey<E>, R1CSVerifierKey<E>), Error> {
        let max_degree = Self::get_max_degree(cs.get_size());
        assert!(pp.powers_of_g.len() > max_degree);

        let mut powers_of_g = Vec::<E::G1Affine>::new();
        // The prover needs both the lowest `max_degree` powers of g,
        // and the highest `max_degree` powers of g, to make sure that
        // some polynomials are bounded by particular degree bounds
        // To save space, store all the needed powers of g in the same
        // vector, because the lower part and the higher part may share
        // common powers of g.
        if pp.powers_of_g.len() >= 2 * (max_degree + 1) {
            powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
            powers_of_g.append(&mut pp.powers_of_g[pp.powers_of_g.len()-max_degree-1..].to_vec());
        } else {
            powers_of_g = pp.powers_of_g[..].to_vec();
        }
        let size = cs.get_size();
        let H=size.nrows as i64;
        let K=size.ncols as i64;
        let S=size.density as i64;
        let ell=size.input_size as i64;
        let gamma=generator_of!(E);
        let M_mat=(cs.arows.iter().map(|a| *a).chain(cs.brows.iter().map(|&i| i + H as u64)).chain(cs.crows.iter().map(|&i| i + H as u64 * 2)).collect::<Vec<u64>>(), cs.acols.iter().chain(cs.bcols.iter()).chain(cs.ccols.iter()).map(|a| *a).collect::<Vec<u64>>(), cs.avals.iter().chain(cs.bvals.iter()).chain(cs.cvals.iter()).map(|a| *a).collect::<Vec<E::Fr>>());
        let u_vec=int_array_to_power_vector!(M_mat.0, gamma);
        let w_vec=int_array_to_power_vector!(M_mat.1, gamma);
        let v_vec=M_mat.2.to_vec();
        let y_vec=u_vec.iter().zip(w_vec.iter()).map(|(a, b)| *a * *b).collect::<Vec<E::Fr>>();
        let cm_u_vec=vector_to_commitment::<E>(&powers_of_g, &u_vec).unwrap();
        let cm_w_vec=vector_to_commitment::<E>(&powers_of_g, &w_vec).unwrap();
        let cm_v_vec=vector_to_commitment::<E>(&powers_of_g, &v_vec).unwrap();
        let cm_y_vec=vector_to_commitment::<E>(&powers_of_g, &y_vec).unwrap();
        
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
            D: pp.powers_of_g.len() as u64,
        };
        Ok((R1CSProverKey::<E> {
            verifier_key: verifier_key.clone(),
            powers: powers_of_g,
            max_degree: max_degree as u64,
            M_mat: M_mat,
            u_vec: u_vec,
            w_vec: w_vec,
            v_vec: v_vec,
            y_vec: y_vec,
        }, verifier_key))
    }
    fn prove(pk: &Self::PK, x: &Self::Ins, w: &Self::Wit) -> Result<Self::Pf, Error> {
        let size = pk.verifier_key.size.clone();
        let vk = pk.verifier_key.clone();
        let D = pk.verifier_key.D as i64;
        let rng = &mut test_rng();
        let H=size.nrows as i64;
        let K=size.ncols as i64;
        let S=size.density as i64;
        let ell=size.input_size as i64;
        let gamma=generator_of!(E);
        let x_vec=x.instance.clone();
        let delta_vec=sample_vec::<E::Fr, _>(rng, 1);
        let delta_vec_1=sample_vec::<E::Fr, _>(rng, 1);
        let delta_vec_2=sample_vec::<E::Fr, _>(rng, 1);
        let delta_vec_3=sample_vec::<E::Fr, _>(rng, 1);
        let delta_vec_4=sample_vec::<E::Fr, _>(rng, 1);
        let w_vec=w.witness.clone();
        let u_vec_1=sparse_mvp(H, K, &pk.M_mat.1, &pk.M_mat.0, &pk.M_mat.2, &vector_concat!(vec![E::Fr::one()], x_vec, w_vec)).unwrap();
        let u_vec_1=fixed_length_vector_iter(&u_vec_1, K + 3*S).chain(delta_vec).collect::<Vec<E::Fr>>();
        let cm_u_vec_1=vector_to_commitment::<E>(&pk.powers, &u_vec_1).unwrap();
        let u_vec_1_poly=poly_from_vec!(u_vec_1);
        let mu=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1).unwrap());
        let mut r_vec=(1..=3*H).map(|i| mu-power(gamma, i)).collect::<Vec<E::Fr>>();
        batch_inversion(&mut r_vec);
        let c_vec=sparse_mvp(K, 3*H, &pk.M_mat.1, &pk.M_mat.0, &pk.M_mat.2, &r_vec).unwrap();
        let s_vec=r_vec.iter().map(|a| *a).chain(r_vec.iter().map(|a| -*a)).collect::<Vec<E::Fr>>();
        let s_vec=fixed_length_vector_iter(&s_vec, K + 3*S).chain(delta_vec_1).collect::<Vec<E::Fr>>();
        let cm_s_vec=vector_to_commitment::<E>(&pk.powers, &s_vec).unwrap();
        let s_vec_poly=poly_from_vec!(s_vec);
        let nu=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec).unwrap());
        let mut rnu_vec=(1..=K).map(|i| nu-power(gamma, i)).collect::<Vec<E::Fr>>();
        batch_inversion(&mut rnu_vec);
        let h_vec=rnu_vec.iter().map(|a| *a).chain(pk.u_vec.iter().map(|a| *a).zip(pk.w_vec.iter().map(|a| *a)).map(|(u, w)| (mu - u) * (nu - w))).collect::<Vec<E::Fr>>();
        let h_vec=fixed_length_vector_iter(&h_vec, K + 3*S).chain(delta_vec_2).collect::<Vec<E::Fr>>();
        let cm_h_vec=vector_to_commitment::<E>(&pk.powers, &h_vec).unwrap();
        let h_vec_poly=poly_from_vec!(h_vec);
        let beta=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec).unwrap());
        define_vec!(r_vec_1, expression_vector!(i, power_linear_combination!(beta, (linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(u_vec_1, (i as i64)-(-3*H + 3*S + 1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(s_vec, (i as i64)-(-3*H + 3*S + 1) as i64+1))), ((linear_combination!(E::Fr::zero(), -to_field::<E::Fr>(1), vector_index!(h_vec, (i as i64)-(3*S + 1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(s_vec, (i as i64)-(-3*H + 3*S + 1) as i64+1))))-((linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(h_vec, (i as i64)-(1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(pk.v_vec, (i as i64)-(K + 1) as i64+1))))), K + 3*S));
        define_vec!(r_vec_tilde, vector_concat!(delta_vec_3, accumulate_vector!(r_vec_1, +)));
        let r_vec_tilde_poly=poly_from_vec!(r_vec_tilde);
        let cm_r_vec_tilde=vector_to_commitment::<E>(&pk.powers, &r_vec_tilde).unwrap();
        let alpha=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde).unwrap());
        define_vec!(t_vec, expression_vector!(i, sum!((linear_combination!(E::Fr::zero(), mu, power_vector_index!(to_field::<E::Fr>(1), 3*H, K + 3*S + i-(1)+1), -to_field::<E::Fr>(1), power_vector_index!(gamma, 3*H, K + 3*S + i-(1)+1)))*(vector_index!(s_vec, K + 3*S + i)), (linear_combination!(E::Fr::zero(), -to_field::<E::Fr>(1), power_vector_index!(to_field::<E::Fr>(1), 3*H, K + 3*S + i-(1)+1)))*(power_vector_index!(to_field::<E::Fr>(1), 3*H, K + 3*S + i)), (linear_combination!(E::Fr::zero(), alpha*nu, power_vector_index!(to_field::<E::Fr>(1), K, K + 3*S + i-(1)+1), -alpha, power_vector_index!(gamma, K, K + 3*S + i-(1)+1)))*(vector_index!(h_vec, K + 3*S + i)), (linear_combination!(E::Fr::zero(), -alpha, power_vector_index!(to_field::<E::Fr>(1), K, K + 3*S + i-(1)+1)))*(power_vector_index!(to_field::<E::Fr>(1), K, K + 3*S + i)), (linear_combination!(E::Fr::zero(), power(alpha, 2), vector_index!(h_vec, (K + 3*S + i as i64)-(1) as i64+1)))*(linear_combination!(linear_combination!(E::Fr::zero(), mu*nu, power_vector_index!(to_field::<E::Fr>(1), K, K + 3*S + i-(K + 1)+1)), -mu, vector_index!(pk.w_vec, (K + 3*S + i as i64)-(K + 1) as i64+1), -nu, vector_index!(pk.u_vec, (K + 3*S + i as i64)-(K + 1) as i64+1), to_field::<E::Fr>(1), vector_index!(pk.y_vec, (K + 3*S + i as i64)-(K + 1) as i64+1))), (linear_combination!(E::Fr::zero(), -power(alpha, 2), power_vector_index!(to_field::<E::Fr>(1), K, K + 3*S + i-(1)+1)))*(power_vector_index!(to_field::<E::Fr>(1), K, K + 3*S + i)), (linear_combination!(E::Fr::zero(), power(alpha, 3), vector_index!(u_vec_1, (K + 3*S + i as i64)-(-H + K + 3*S + 1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(u_vec_1, (K + 3*S + i as i64)-(-2*H + K + 3*S + 1) as i64+1))), (linear_combination!(E::Fr::zero(), -power(alpha, 3), power_vector_index!(to_field::<E::Fr>(1), H, K + 3*S + i-(-H + K + 3*S + 1)+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(u_vec_1, (K + 3*S + i as i64)-(-3*H + K + 3*S + 1) as i64+1))), (linear_combination!(E::Fr::zero(), power(alpha, 5), vector_index!(u_vec_1, (K + 3*S + i as i64)-(-3*H + 3*S + 1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(s_vec, (K + 3*S + i as i64)-(-3*H + 3*S + 1) as i64+1))), (linear_combination!(E::Fr::zero(), -power(alpha, 5)*beta, vector_index!(h_vec, (K + 3*S + i as i64)-(3*S + 1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(s_vec, (K + 3*S + i as i64)-(-3*H + 3*S + 1) as i64+1))), (linear_combination!(E::Fr::zero(), -power(alpha, 5)*beta, vector_index!(h_vec, (K + 3*S + i as i64)-(1) as i64+1)))*(linear_combination!(E::Fr::zero(), to_field::<E::Fr>(1), vector_index!(pk.v_vec, (K + 3*S + i as i64)-(K + 1) as i64+1))), (linear_combination!(E::Fr::zero(), -power(alpha, 5), vector_index!(r_vec_tilde, (K + 3*S + i as i64)-(1) as i64+1), power(alpha, 5), vector_index!(r_vec_tilde, (K + 3*S + i as i64)-(2) as i64+1)))*(power_vector_index!(to_field::<E::Fr>(1), K + 3*S, K + 3*S + i))), 3*S + 2));
        define_vec!(t_vec_1, vector_concat!(t_vec, delta_vec_4));
        let cm_t_vec_1=vector_to_commitment::<E>(&pk.powers, &t_vec_1).unwrap();
        let omega=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1).unwrap());
        let v_vec_1=vector_poly_mul!(h_vec, pk.w_vec, omega).coeffs;
        let shiftlength=h_vec.len() as i64 -1;
        let v_vec_2=vector_reverse_omega!(h_vec, omega);
        let shiftlength_1=h_vec.len() as i64 -1;
        let v_vec_3=vector_poly_mul!(h_vec, pk.u_vec, omega).coeffs;
        let shiftlength_2=h_vec.len() as i64 -1;
        let v_vec_4=vector_poly_mul!(h_vec, pk.y_vec, omega).coeffs;
        let shiftlength_3=h_vec.len() as i64 -1;
        let v_vec_5=vector_poly_mul!(u_vec_1, u_vec_1, omega).coeffs;
        let shiftlength_4=u_vec_1.len() as i64 -1;
        let v_vec_6=vector_poly_mul!(u_vec_1, s_vec, omega).coeffs;
        let shiftlength_5=u_vec_1.len() as i64 -1;
        let v_vec_7=vector_poly_mul!(h_vec, s_vec, omega).coeffs;
        let shiftlength_6=h_vec.len() as i64 -1;
        let v_vec_8=vector_poly_mul!(h_vec, pk.v_vec, omega).coeffs;
        let shiftlength_7=h_vec.len() as i64 -1;
        let v_vec_9=vector_reverse_omega!(r_vec_tilde, omega);
        let shiftlength_8=r_vec_tilde.len() as i64 -1;
        let v_vec_10=vector_power_mul!(s_vec, omega.inverse().unwrap(), 3*H);
        let v_vec_11=vector_power_mul!(s_vec, to_field::<E::Fr>(1)/(gamma*omega), 3*H);
        let v_vec_12=vector_power_mul!(h_vec, omega.inverse().unwrap(), K);
        let v_vec_13=vector_power_mul!(h_vec, to_field::<E::Fr>(1)/(gamma*omega), K);
        let v_vec_14=vector_power_mul!(v_vec_2, to_field::<E::Fr>(1), K);
        let v_vec_15=vector_power_mul!(u_vec_1, omega.inverse().unwrap(), H);
        let v_vec_16=vector_power_mul!(u_vec_1, omega.inverse().unwrap(), ell + 1);
        let v_vec_17=vector_power_mul!(x_vec, omega.inverse().unwrap(), ell + 1);
        let v_vec_18=vector_power_mul!(v_vec_9, to_field::<E::Fr>(1), K + 3*S);
        let v_vec_19=vector_power_mul!(t_vec_1, omega.inverse().unwrap(), 3*S + 1);
        let v_vec_20=power_power_mul!(to_field::<E::Fr>(1), 3*H, to_field::<E::Fr>(1), 3*H);
        let v_vec_21=power_power_mul!(to_field::<E::Fr>(1), K, to_field::<E::Fr>(1), K);
        let v_vec_22=power_power_mul!(to_field::<E::Fr>(1), K, to_field::<E::Fr>(1), K);
        let h_vec_2=expression_vector!(i, linear_combination!(linear_combination!(E::Fr::zero(), -power(alpha, 4)*power(omega, 3*H + ell), power_vector_index!(omega.inverse().unwrap(), ell + 1, -K - 6*S + i - 1-(1 - ell)+1)), -power(alpha, 2)*mu, vector_index!(v_vec_1, (-K - 6*S + i - 1 as i64)-(K - shiftlength + 1) as i64+1), -power(alpha, 2)*nu, vector_index!(v_vec_3, (-K - 6*S + i - 1 as i64)-(K - shiftlength_2 + 1) as i64+1), power(alpha, 2), vector_index!(v_vec_4, (-K - 6*S + i - 1 as i64)-(K - shiftlength_3 + 1) as i64+1), power(alpha, 3)*power(omega, -H + K + 3*S), vector_index!(v_vec_5, (-K - 6*S + i - 1 as i64)-(-H - shiftlength_4 + 1) as i64+1), power(alpha, 5)*power(omega, -3*H + 3*S), vector_index!(v_vec_6, (-K - 6*S + i - 1 as i64)-(1 - shiftlength_5) as i64+1), -power(alpha, 5)*beta*power(omega, 3*S), vector_index!(v_vec_7, (-K - 6*S + i - 1 as i64)-(-3*H - shiftlength_6 + 1) as i64+1), -power(alpha, 5)*beta, vector_index!(v_vec_8, (-K - 6*S + i - 1 as i64)-(K - shiftlength_7 + 1) as i64+1), power(alpha, 6), vector_index!(v_vec_9, (-K - 6*S + i - 1 as i64)-(K + 3*S - shiftlength_8) as i64+1), mu*power(omega, 3*H - 1), vector_index!(v_vec_10, (-K - 6*S + i - 1 as i64)-(2 - 3*H) as i64+1), -power(gamma*omega, 3*H - 1), vector_index!(v_vec_11, (-K - 6*S + i - 1 as i64)-(2 - 3*H) as i64+1), alpha*nu*power(omega, K - 1), vector_index!(v_vec_12, (-K - 6*S + i - 1 as i64)-(2 - K) as i64+1), -alpha*power(gamma*omega, K - 1), vector_index!(v_vec_13, (-K - 6*S + i - 1 as i64)-(2 - K) as i64+1), power(alpha, 2)*mu*nu, vector_index!(v_vec_14, (-K - 6*S + i - 1 as i64)-(K - shiftlength_1 + 1) as i64+1), -power(alpha, 3)*power(omega, K + 3*S - 1), vector_index!(v_vec_15, (-K - 6*S + i - 1 as i64)-(2 - 3*H) as i64+1), power(alpha, 4)*power(omega, 3*H + ell), vector_index!(v_vec_16, (-K - 6*S + i - 1 as i64)-(-3*H - ell + 1) as i64+1), -power(alpha, 4)*power(omega, 3*H + ell), vector_index!(v_vec_17, (-K - 6*S + i - 1 as i64)-(2 - ell) as i64+1), -power(alpha, 5), vector_index!(v_vec_18, (-K - 6*S + i - 1 as i64)-(1 - shiftlength_8) as i64+1), power(alpha, 5)*omega, vector_index!(v_vec_18, (-K - 6*S + i - 1 as i64)-(-shiftlength_8) as i64+1), -power(omega, K + 6*S), vector_index!(v_vec_19, (-K - 6*S + i - 1 as i64)-(-3*S) as i64+1), -to_field::<E::Fr>(1), vector_index!(v_vec_20, (-K - 6*S + i - 1 as i64)-(1) as i64+1), -alpha, vector_index!(v_vec_21, (-K - 6*S + i - 1 as i64)-(1) as i64+1), -power(alpha, 2), vector_index!(v_vec_22, (-K - 6*S + i - 1 as i64)-(1) as i64+1)), K + 6*S + 1);
        let h_vec_3=expression_vector!(i, linear_combination!(linear_combination!(E::Fr::zero(), -power(alpha, 4)*power(omega, 3*H + ell), power_vector_index!(omega.inverse().unwrap(), ell + 1, i-(1 - ell)+1)), -power(alpha, 2)*mu, vector_index!(v_vec_1, (i as i64)-(K - shiftlength + 1) as i64+1), -power(alpha, 2)*nu, vector_index!(v_vec_3, (i as i64)-(K - shiftlength_2 + 1) as i64+1), power(alpha, 2), vector_index!(v_vec_4, (i as i64)-(K - shiftlength_3 + 1) as i64+1), power(alpha, 3)*power(omega, -H + K + 3*S), vector_index!(v_vec_5, (i as i64)-(-H - shiftlength_4 + 1) as i64+1), power(alpha, 5)*power(omega, -3*H + 3*S), vector_index!(v_vec_6, (i as i64)-(1 - shiftlength_5) as i64+1), -power(alpha, 5)*beta*power(omega, 3*S), vector_index!(v_vec_7, (i as i64)-(-3*H - shiftlength_6 + 1) as i64+1), -power(alpha, 5)*beta, vector_index!(v_vec_8, (i as i64)-(K - shiftlength_7 + 1) as i64+1), power(alpha, 6), vector_index!(v_vec_9, (i as i64)-(K + 3*S - shiftlength_8) as i64+1), mu*power(omega, 3*H - 1), vector_index!(v_vec_10, (i as i64)-(2 - 3*H) as i64+1), -power(gamma*omega, 3*H - 1), vector_index!(v_vec_11, (i as i64)-(2 - 3*H) as i64+1), alpha*nu*power(omega, K - 1), vector_index!(v_vec_12, (i as i64)-(2 - K) as i64+1), -alpha*power(gamma*omega, K - 1), vector_index!(v_vec_13, (i as i64)-(2 - K) as i64+1), power(alpha, 2)*mu*nu, vector_index!(v_vec_14, (i as i64)-(K - shiftlength_1 + 1) as i64+1), -power(alpha, 3)*power(omega, K + 3*S - 1), vector_index!(v_vec_15, (i as i64)-(2 - 3*H) as i64+1), power(alpha, 4)*power(omega, 3*H + ell), vector_index!(v_vec_16, (i as i64)-(-3*H - ell + 1) as i64+1), -power(alpha, 4)*power(omega, 3*H + ell), vector_index!(v_vec_17, (i as i64)-(2 - ell) as i64+1), -power(alpha, 5), vector_index!(v_vec_18, (i as i64)-(1 - shiftlength_8) as i64+1), power(alpha, 5)*omega, vector_index!(v_vec_18, (i as i64)-(-shiftlength_8) as i64+1), -power(omega, K + 6*S), vector_index!(v_vec_19, (i as i64)-(-3*S) as i64+1), -to_field::<E::Fr>(1), vector_index!(v_vec_20, (i as i64)-(1) as i64+1), -alpha, vector_index!(v_vec_21, (i as i64)-(1) as i64+1), -power(alpha, 2), vector_index!(v_vec_22, (i as i64)-(1) as i64+1)), K + 6*S + 1);
        let cm_h_vec_2=vector_to_commitment::<E>(&pk.powers, &h_vec_2).unwrap();
        let cm_h_vec_3=vector_to_commitment::<E>(&pk.powers, &h_vec_3).unwrap();
        let z=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1, cm_h_vec_2, cm_h_vec_3).unwrap());
        let y=eval_vector_expression!(omega/z, i, vector_index!(h_vec, i), K + 3*S + 1);
        let y_1=eval_vector_expression!(omega/z, i, vector_index!(u_vec_1, i), K + 3*S + 1);
        let y_2=eval_vector_expression!(omega/z, i, vector_index!(r_vec_tilde, i), K + 3*S + 1);
        let c=sum!(z*(mu*(E::Fr::one() - power(omega/z, 3*H))*(E::Fr::one()*z - gamma*omega) - (E::Fr::one() - power(gamma*omega/z, 3*H))*(E::Fr::one()*z - omega))/((E::Fr::one()*z - omega)*(E::Fr::one()*z - gamma*omega)), power(alpha, 5)*y_1*power(z, -3*H + 3*S)*power(omega/z, -3*H + 3*S), -power(alpha, 5)*beta*y*power(z, -3*H + 3*S)*power(omega/z, 3*S));
        let c_1=sum!(-z*(E::Fr::one() - power(z, 3*H))*(E::Fr::one() - power(omega/z, 3*H))/((E::Fr::one() - z)*(E::Fr::one()*z - omega)), -alpha*z*(E::Fr::one() - power(z, K))*(E::Fr::one() - power(omega/z, K))/((E::Fr::one() - z)*(E::Fr::one()*z - omega)), power(alpha, 2)*mu*nu*y*power(z, K)*(E::Fr::one() - power(z, K))/(E::Fr::one() - z), -power(alpha, 2)*z*(E::Fr::one() - power(z, K))*(E::Fr::one() - power(omega/z, K))/((E::Fr::one() - z)*(E::Fr::one()*z - omega)), (power(alpha, 4)*power(z, 3*H + 2)*power(omega/z, 3*H)*(-E::Fr::one() + power(omega/z, ell + 1))/(E::Fr::one()*z - omega)) * (eval_vector_expression!(z, i, vector_index!(x_vec, i), ell)), power(alpha, 4)*power(z, 3*H + 1)*power(omega/z, 3*H)*(-E::Fr::one() + power(omega/z, ell + 1))/(E::Fr::one()*z - omega), power(alpha, 5)*y_2*(E::Fr::one() - power(z, K + 3*S))*(omega - z)/(z*(E::Fr::one() - z)), power(alpha, 6)*y_2*power(z, K + 3*S - 1));
        let c_2=alpha*z*(nu*(E::Fr::one() - power(omega/z, K))*(E::Fr::one()*z - gamma*omega) - (E::Fr::one() - power(gamma*omega/z, K))*(E::Fr::one()*z - omega))/((E::Fr::one()*z - omega)*(E::Fr::one()*z - gamma*omega));
        let c_3=-power(alpha, 2)*mu*y*power(z, K);
        let c_4=-power(alpha, 2)*nu*y*power(z, K);
        let c_5=power(alpha, 2)*y*power(z, K);
        let c_6=sum!(power(alpha, 3)*y_1*power(z, -2*H + K + 3*S)*power(omega/z, -H + K + 3*S), power(alpha, 3)*power(z, -3*H + K + 3*S + 1)*power(omega/z, -H + K + 3*S)*(-E::Fr::one() + power(omega/z, H))/(E::Fr::one()*z - omega), power(alpha, 4)*z*power(omega/z, 3*H)*(E::Fr::one() - power(omega/z, ell + 1))/(E::Fr::one()*z - omega));
        let c_7=-power(alpha, 5)*beta*y*power(z, K);
        let c_8=power(z, K + 3*S)*power(omega/z, K + 3*S)*(-E::Fr::one() + power(omega/z, 3*S + 1))/(E::Fr::one()*z - omega);
        let c_9=-power(z, D);
        let c_10=-z;
        let mut g_poly=expression_vector!(i, sum!((c) * (vector_index!(s_vec, i)), (c_2) * (vector_index!(h_vec, i)), (c_3) * (vector_index!(pk.w_vec, i)), (c_4) * (vector_index!(pk.u_vec, i)), (c_5) * (vector_index!(pk.y_vec, i)), (c_6) * (vector_index!(u_vec_1, i)), (c_7) * (vector_index!(pk.v_vec, i)), (c_8) * (vector_index!(t_vec_1, i)), (c_9) * (vector_index!(h_vec_2, i)), (c_10) * (vector_index!(h_vec_3, i))), K + 3*S + 1);
        g_poly[0]+=c_1;
        let g_poly=poly_from_vec!(g_poly);
        let cm_g=Commitment::<E>(sum!((cm_s_vec.0).mul(c.into_repr()), (cm_h_vec.0).mul(c_2.into_repr()), (vk.cm_w_vec.0).mul(c_3.into_repr()), (vk.cm_u_vec.0).mul(c_4.into_repr()), (vk.cm_y_vec.0).mul(c_5.into_repr()), (cm_u_vec_1.0).mul(c_6.into_repr()), (vk.cm_v_vec.0).mul(c_7.into_repr()), (cm_t_vec_1.0).mul(c_8.into_repr()), (cm_h_vec_2.0).mul(c_9.into_repr()), (cm_h_vec_3.0).mul(c_10.into_repr()), scalar_to_commitment::<E>(&vk.kzg_vk.g, &c_10).unwrap().0.into_projective()).into_affine());
        let fs=vec!(h_vec_poly, u_vec_1_poly, r_vec_tilde_poly);
        let gs=vec!(g_poly);
        let zz=z;
        let z=omega/z;
        let rand_xi=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1, cm_h_vec_2, cm_h_vec_3, cm_g, omega/z, y, y_1, y_2, z).unwrap());
        let rand_xi_2=hash_to_field::<E::Fr>(to_bytes!(x_vec, pk.verifier_key.cm_u_vec, pk.verifier_key.cm_w_vec, pk.verifier_key.cm_v_vec, pk.verifier_key.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1, cm_h_vec_2, cm_h_vec_3, cm_g, omega/z, y, y_1, y_2, z).unwrap());
        
        let (W, W_1) = KZG10::batch_open(
            &pk.powers,
            &fs,
            &gs,
            &z,
            &zz,
            &rand_xi,
            &rand_xi_2,
        )?;
        Ok(R1CSProof::<E> {
            cm_u_vec_1: cm_u_vec_1,
            cm_s_vec: cm_s_vec,
            cm_h_vec: cm_h_vec,
            cm_r_vec_tilde: cm_r_vec_tilde,
            cm_t_vec_1: cm_t_vec_1,
            cm_h_vec_2: cm_h_vec_2,
            cm_h_vec_3: cm_h_vec_3,
            y: y,
            y_1: y_1,
            y_2: y_2,
            W: W,
            W_1: W_1,
        })
    }
    fn verify(vk: &Self::VK, x: &Self::Ins, proof: &Self::Pf) -> Result<(), Error> {
        let size = vk.size.clone();
        let D = vk.D as i64;
        let rng = &mut test_rng();
        let cm_u_vec_1 = proof.cm_u_vec_1;
        let cm_s_vec = proof.cm_s_vec;
        let cm_h_vec = proof.cm_h_vec;
        let cm_r_vec_tilde = proof.cm_r_vec_tilde;
        let cm_t_vec_1 = proof.cm_t_vec_1;
        let cm_h_vec_2 = proof.cm_h_vec_2;
        let cm_h_vec_3 = proof.cm_h_vec_3;
        let y = proof.y;
        let y_1 = proof.y_1;
        let y_2 = proof.y_2;
        let W = proof.W;
        let W_1 = proof.W_1;let H=size.nrows as i64;
        let K=size.ncols as i64;
        let S=size.density as i64;
        let ell=size.input_size as i64;
        let gamma=generator_of!(E);
        let x_vec=x.instance.clone();
        let mu=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1).unwrap());
        let nu=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec).unwrap());
        let beta=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec).unwrap());
        let alpha=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde).unwrap());
        let omega=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1).unwrap());
        let z=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1, cm_h_vec_2, cm_h_vec_3).unwrap());
        let c=sum!(z*(mu*(E::Fr::one() - power(omega/z, 3*H))*(E::Fr::one()*z - gamma*omega) - (E::Fr::one() - power(gamma*omega/z, 3*H))*(E::Fr::one()*z - omega))/((E::Fr::one()*z - omega)*(E::Fr::one()*z - gamma*omega)), power(alpha, 5)*y_1*power(z, -3*H + 3*S)*power(omega/z, -3*H + 3*S), -power(alpha, 5)*beta*y*power(z, -3*H + 3*S)*power(omega/z, 3*S));
        let c_1=sum!(-z*(E::Fr::one() - power(z, 3*H))*(E::Fr::one() - power(omega/z, 3*H))/((E::Fr::one() - z)*(E::Fr::one()*z - omega)), -alpha*z*(E::Fr::one() - power(z, K))*(E::Fr::one() - power(omega/z, K))/((E::Fr::one() - z)*(E::Fr::one()*z - omega)), power(alpha, 2)*mu*nu*y*power(z, K)*(E::Fr::one() - power(z, K))/(E::Fr::one() - z), -power(alpha, 2)*z*(E::Fr::one() - power(z, K))*(E::Fr::one() - power(omega/z, K))/((E::Fr::one() - z)*(E::Fr::one()*z - omega)), (power(alpha, 4)*power(z, 3*H + 2)*power(omega/z, 3*H)*(-E::Fr::one() + power(omega/z, ell + 1))/(E::Fr::one()*z - omega)) * (eval_vector_expression!(z, i, vector_index!(x_vec, i), ell)), power(alpha, 4)*power(z, 3*H + 1)*power(omega/z, 3*H)*(-E::Fr::one() + power(omega/z, ell + 1))/(E::Fr::one()*z - omega), power(alpha, 5)*y_2*(E::Fr::one() - power(z, K + 3*S))*(omega - z)/(z*(E::Fr::one() - z)), power(alpha, 6)*y_2*power(z, K + 3*S - 1));
        let c_2=alpha*z*(nu*(E::Fr::one() - power(omega/z, K))*(E::Fr::one()*z - gamma*omega) - (E::Fr::one() - power(gamma*omega/z, K))*(E::Fr::one()*z - omega))/((E::Fr::one()*z - omega)*(E::Fr::one()*z - gamma*omega));
        let c_3=-power(alpha, 2)*mu*y*power(z, K);
        let c_4=-power(alpha, 2)*nu*y*power(z, K);
        let c_5=power(alpha, 2)*y*power(z, K);
        let c_6=sum!(power(alpha, 3)*y_1*power(z, -2*H + K + 3*S)*power(omega/z, -H + K + 3*S), power(alpha, 3)*power(z, -3*H + K + 3*S + 1)*power(omega/z, -H + K + 3*S)*(-E::Fr::one() + power(omega/z, H))/(E::Fr::one()*z - omega), power(alpha, 4)*z*power(omega/z, 3*H)*(E::Fr::one() - power(omega/z, ell + 1))/(E::Fr::one()*z - omega));
        let c_7=-power(alpha, 5)*beta*y*power(z, K);
        let c_8=power(z, K + 3*S)*power(omega/z, K + 3*S)*(-E::Fr::one() + power(omega/z, 3*S + 1))/(E::Fr::one()*z - omega);
        let c_9=-power(z, D);
        let c_10=-z;
        let cm_g=Commitment::<E>(sum!((cm_s_vec.0).mul(c.into_repr()), (cm_h_vec.0).mul(c_2.into_repr()), (vk.cm_w_vec.0).mul(c_3.into_repr()), (vk.cm_u_vec.0).mul(c_4.into_repr()), (vk.cm_y_vec.0).mul(c_5.into_repr()), (cm_u_vec_1.0).mul(c_6.into_repr()), (vk.cm_v_vec.0).mul(c_7.into_repr()), (cm_t_vec_1.0).mul(c_8.into_repr()), (cm_h_vec_2.0).mul(c_9.into_repr()), (cm_h_vec_3.0).mul(c_10.into_repr()), scalar_to_commitment::<E>(&vk.kzg_vk.g, &c_10).unwrap().0.into_projective()).into_affine());
        let rand_xi=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1, cm_h_vec_2, cm_h_vec_3, cm_g, omega/z, y, y_1, y_2, z).unwrap());
        let rand_xi_2=hash_to_field::<E::Fr>(to_bytes!(x_vec, vk.cm_u_vec, vk.cm_w_vec, vk.cm_v_vec, vk.cm_y_vec, cm_u_vec_1, cm_s_vec, cm_h_vec, cm_r_vec_tilde, cm_t_vec_1, cm_h_vec_2, cm_h_vec_3, cm_g, omega/z, y, y_1, y_2, z).unwrap());
        let zz=z;
        let z=omega/z;
        let f_commitments=vec!(cm_h_vec, cm_u_vec_1, cm_r_vec_tilde);
        let g_commitments=vec!(cm_g);
        let f_values=vec!(y, y_1, y_2);
        let g_values=vec!(E::Fr::zero());
        
        if KZG10::<E, DensePoly<E::Fr>>::batch_check(
            &vk.kzg_vk,
            &f_commitments,
            &g_commitments,
            &z,
            &zz,
            &rand_xi,
            &rand_xi_2,
            &f_values,
            &g_values,
            &proof.W,
            &proof.W_1,
            rng,
        )? {
            Ok(())
        } else {
            Err(Error::VerificationFail)
        }
    }
}


