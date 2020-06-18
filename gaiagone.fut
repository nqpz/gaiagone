import "lib/github.com/diku-dk/lys/lys"
import "lib/github.com/diku-dk/cpprandom/random"
import "lib/github.com/athas/vector/vspace"

module vec2 = mk_vspace_2d f32
module rnge = minstd_rand
module dist = uniform_real_distribution f32 rnge
type rng = rnge.rng

let n_planets = 10i32

let granularity = 50i32

let max_spike_diff_factor = 2.0f32

let particle_mass = 0.00005f32

type point = vec2.vector

type particle = {p: point, pd: point, color: argb.colour}

type spike = {size: f32, color: argb.colour}

type planet = {center: point,
               spikes: [granularity]spike}

type collision_info = {has_collision: bool,
                       spike0: (i32, f32), spike1: (i32, f32)}

let point_sum: []point -> point = reduce_comm (vec2.+) {y=0, x=0}

let binary_search (goal: f32) (delta_goal: f32) (lower_init: f32) (upper_init: f32)
                  (max_iter: i32) (f: f32 -> f32): (f32, i32) =
  let pick (lower: f32) (upper: f32): f32 = lower + (upper - lower) / 2
  let inp_init = pick lower_init upper_init
  let (inp, _, _, _, n_iters) =
    loop (inp, res, lower, upper, i) = (inp_init, f inp_init, lower_init, upper_init, 0)
    while f32.abs (res - goal) > delta_goal && i < max_iter
    do let (inp', lower', upper') =
         if res > goal
         then (pick lower inp, lower, inp)
         else (pick inp upper, inp, upper)
       in (inp', f inp', lower', upper', i + 1)
  in (inp, n_iters)

let newton_solve (f: f32 -> f32) (f': f32 -> f32) (delta_goal: f32) (max_iter: i32) (initial: f32): f32 =
  let (res, _n_iters) =
    loop (x, i) = (initial, 0)
    while f32.abs x > delta_goal && i < max_iter
    do (x - f x / f' x, i + 1)
  in res

let find_spike_idx (pl: planet) (po: point): (i32, f32, f32) =
  let rel = po vec2.- pl.center
  let dist = f32.sqrt (rel.y**2 + rel.x**2)
  let degrees = f32.atan2 rel.y rel.x
  let spike_idx_base = r32 granularity * ((degrees + f32.pi) / (2 * f32.pi))
  in (t32 spike_idx_base % granularity, spike_idx_base % 1, dist)

let check_collision (pl: planet) (po: point): collision_info =
  let (spike_idx0, spike_idx_favor1, dist) = find_spike_idx pl po
  let spike_idx1 = (spike_idx0 + 1) % granularity
  let spike_idx_favor0 = 1 - spike_idx_favor1
  let spike = pl.spikes[spike_idx0].size * spike_idx_favor0 +
              pl.spikes[spike_idx1].size * spike_idx_favor1
  let has_collision = dist <= spike
  in {has_collision, spike0=(spike_idx0, spike_idx_favor0), spike1=(spike_idx1, spike_idx_favor1)}

let check_collision_movement (pl: planet) (po_from: point) (po_to: point): collision_info =
  -- XXX: It might be faster to not check all spikes, but instead start by
  -- finding all possible spikes that the movement could overlap with.
  -- Something like this, and then interpolating the inbetween indices:
  --
  --   let (spike_idx_start, spike_idx_end) = ((find_spike_idx pl po_from).0, (find_spike_idx pl po_to).0)
  --
  -- Special care needs to be taken w.r.t. the interpolation, as the indices
  -- wrap around (since it's a circle).

  let find_t ((i0, s0): (i32, spike)) ((i1, s1): (i32, spike)): [](f32, collision_info) =
    let (size0, size1) = (s0.size, s1.size)
    let (deg0, deg1) = ((2 * f32.pi / r32 granularity) * r32 i0 + f32.pi,
                        (2 * f32.pi / r32 granularity) * r32 i1 + f32.pi)

    let t0_div = size0 * f32.cos deg0 + po_from.x + po_to.x - pl.center.x
    let (t0_possible, t0) = if t0_div != 0
                            then (true, (po_from.x - pl.center.x) / t0_div)
                            else (false, f32.nan)
    let t0_ok = t0_possible && 0 <= t0 && t0 < 1
    let t0_info = {has_collision=t0_ok, spike0=(i0, 1), spike1=(i1, 0)}

    let t1_div = size1 * f32.cos deg1 + po_from.x + po_to.x - pl.center.x
    let (t1_possible, t1) = if t1_div != 0
                            then (true, (po_from.x - pl.center.x) / t1_div)
                            else (false, f32.nan)
    let t1_ok = t1_possible && 0 <= t1 && t1 < 1
    let t1_info = {has_collision=t1_ok, spike0=(i0, 0), spike1=(i1, 1)}

    let t2_f t = ((1 - t) * size0 + t * size1) * f32.cos ((1 - t) * deg0 + t * deg1)
    let t2_f' t = (size1 - size0) * f32.cos (deg0 * (1 - t) + deg1 * t) +
                  (size0 * (1 - t) + size1 * t) * (deg0 - deg1) * f32.sin (deg0 * (1 - t) + deg1 * t)
    let t2 = newton_solve t2_f t2_f' 0.00001 100 0.5
    let t2_ok = 0 <= t2 && t2 < 1
    let t2_info = {has_collision=t2_ok, spike0=(i0, t2), spike1=(i1, 1 - t2)}

    in [(t0, t0_info), (t1, t1_info), (t2, t2_info)]

  let ts = flatten (map (\(i0, i1) -> find_t (i0, pl.spikes[i0]) (i1, pl.spikes[i1]))
                        (map (\i -> (i, (i + 1) % granularity)) (0..<granularity)))
  let empty_collision_info = {has_collision=false, spike0=(-1, 0), spike1=(-1, 0)}
  let (_t, info) = reduce_comm (\(t0, info0) (t1, info1) -> if !info0.has_collision
                                                            then (t1, info1)
                                                            else if !info1.has_collision
                                                            then (t0, info0)
                                                            else if t0 < t1
                                                            then (t0, info0)
                                                            else (t1, info1))
                               (1, empty_collision_info) ts
  in info

let planet_mass' (spike_sizes: []f32): f32 =
  let segments = map (\i -> (i, (i + 1) % granularity)) (0..<length spike_sizes)
  let segment_mass ((i, j): (i32, i32)): f32 =
    let size0 = spike_sizes[i]
    let size1 = spike_sizes[j]
    -- Integrate (size0 i + size1 - i size1)**2 * f32.pi / r32 granularity  for [0..1]:
    let size_integrated i = f32.pi * (i * size0 + size1 - size1 * i)**3 / (r32 granularity * (3 * size0 - 3 * size1))
    in if size0 != size1
       then size_integrated 1 - size_integrated 0
       else size0**2 * f32.pi / r32 granularity
  in f32.sum (map segment_mass segments)

let planet_mass (pl: planet): f32 = planet_mass' (map (.size) pl.spikes)


type debug_info = {factor: f32,
                   factor_lower: f32,
                   factor_upper: f32,
                   n_iters: i32,
                   newly_consumed_mass: f32,
                   planet_mass_theoretical: f32,
                   spike_diff_factor: f32}

type~ state = {planets: [n_planets]planet,
               particles: []particle,
               mouse: {y: i32, x: i32},
               view_zoom: f32, view_center: point,
               rng: rng,
               h: i32, w: i32,
               info_idx: i32,
               debugs: [n_planets]debug_info}

let debug_init (pl: planet): debug_info =
  {factor= -1,
   factor_lower= -1,
   factor_upper= -1,
   n_iters= -1,
   newly_consumed_mass= -1,
   planet_mass_theoretical=planet_mass pl,
   spike_diff_factor= -1}

type text_content = (i32, i32, f32, i32, f32, f32, f32, f32, f32, i32, f32, f32)

let lys_text_format () =
  "FPS: %d\n"
  ++ "Particles: %d\n"
  ++ "Collective particle mass: %f\n"
  ++ "\n"
  ++ "Information about planet %d:\n"
  ++ "Planet mass: %f\n"
  ++ "Theoretical planet mass: %f\n"
  ++ "Factor: %f (lower: %f, upper: %f)\n"
  ++ "Binary search iterations: %d\n"
  ++ "Newly consumed mass: %f\n"
  ++ "Spike diff factor: %f"

let lys_text_content (fps: f32) (s: state): text_content =
  (t32 fps,
   length s.particles,
   particle_mass * r32 (length s.particles),
   s.info_idx,
   planet_mass s.planets[s.info_idx],
   s.debugs[s.info_idx].planet_mass_theoretical,
   s.debugs[s.info_idx].factor,
   s.debugs[s.info_idx].factor_lower,
   s.debugs[s.info_idx].factor_upper,
   s.debugs[s.info_idx].n_iters,
   s.debugs[s.info_idx].newly_consumed_mass,
   s.debugs[s.info_idx].spike_diff_factor)


let gen_planet (rng: rng): (rng, planet) =
  let rngs = rnge.split_rng granularity rng
  let (rngs, spikes) = unzip (map (\rng ->
                                     let (rng, size) = dist.rand (0.05, 0.06) rng
                                     let (rng, r) = dist.rand (0.2, 0.8) rng
                                     let (rng, g) = dist.rand (0.2, 0.8) rng
                                     let (rng, b) = dist.rand (0.2, 0.8) rng
                                     let color = argb.from_rgba r g b 1.0
                                     in (rng, {size, color})) rngs)
  let rng = rnge.join_rng rngs
  let (rng, ycenter) = dist.rand (-4.5, 4.5) rng
  let (rng, xcenter) = dist.rand (-4.5, 4.5) rng
  in (rng, {center={y=ycenter, x=xcenter}, spikes})

let gen_planets (rng: rng): (rng, []planet) =
  let rngs = rnge.split_rng n_planets rng
  let (rngs, planets) = unzip (map gen_planet rngs)
  let rng = rnge.join_rng rngs
  in (rng, planets)

let gen_particles (rng: rng): (rng, []particle) =
  let rngs = rnge.split_rng 100000 rng
  let (rngs, ys) = unzip (map (dist.rand (-4.5, 4.5)) rngs)
  let (rngs, xs) = unzip (map (dist.rand (-4.5, 4.5)) rngs)
  let (rngs, yds) = unzip (map (dist.rand (-0.005, 0.005)) rngs)
  let (rngs, xds) = unzip (map (dist.rand (-0.005, 0.005)) rngs)
  let (rngs, rs) = unzip (map (dist.rand (0.2, 0.8)) rngs)
  let (rngs, gs) = unzip (map (dist.rand (0.2, 0.8)) rngs)
  let (rngs, bs) = unzip (map (dist.rand (0.2, 0.8)) rngs)
  let colors = map3 (\r g b -> argb.from_rgba r g b 1.0) rs gs bs
  let rng = rnge.join_rng rngs
  let ps = map5 (\y x yd xd color -> {p={y, x}, pd={y=yd, x=xd}, color}) ys xs yds xds colors
  in (rng, ps)

let accel (center: point) (mass: f32) (p: point): point =
  if p == center
  then {y=0, x=0}
  else let r = vec2.(center - p)
       let rsqr = vec2.dot r r
       let invr = 1 / f32.sqrt rsqr
       let invr2 = invr * invr
       let s = mass * invr2
       in vec2.scale s r

let color_merge ((color0, factor0): (argb.colour, f32)) ((color1, factor1): (argb.colour, f32)): argb.colour =
  if color0 == 0
  then color1
  else if color1 == 0
  then color0
  else argb.mix factor0 color0 factor1 color1

let step (td: f32) (s: state): state =
  let particles = map (\{p, pd, color} ->
                         let pdd = point_sum (map (\pl -> accel pl.center (planet_mass pl) p) s.planets)
                                   vec2.+ point_sum (map (\part -> accel part.p particle_mass p) s.particles)
                         in {p=vec2.(p + scale td pd), pd=vec2.(pd + scale td pdd), color}) s.particles

-- NOTE: We assume that planets don't overlap, but they do.  Currently, a
-- particle that hits more than one planet counts as having hit all those
-- planets, i.e., we don't have mass conservation in that case.  FIXME: Add
-- planet-planet collision detection.

  let step_planet (pl: planet) (debug_old: debug_info): (planet, debug_info) =
    let collisions = map (check_collision pl <-< (.p)) particles
    -- FIXME: This will solve the tunneling effect once it works.
    -- let collisions = map2 (\part_old part_new -> check_collision_movement pl part_old.p part_new.p) s.particles particles
    let (particles_collisions, _particles_unchanged) = partition ((.has_collision) <-< (.1)) (zip particles collisions)
    in if length particles_collisions == 0
       then (pl, debug_old)
       else let collisions' = map (.1) particles_collisions
            let spike_merge spike0 spike1 =
              {size=spike0.size + spike1.size, color=color_merge (spike0.color, spike0.size) (spike1.color, spike1.size)}
            let spike_empty = {size=0, color=0} -- ignore black, use as special value
            let spikes_empty = map (const spike_empty) pl.spikes
            let n = length collisions' * 2
            let indices = map (.spike0.0) collisions' ++ map (.spike1.0) collisions' :> [n]i32
            let values = map (\pc -> {size=particle_mass * pc.1.spike0.1, color=pc.0.color}) particles_collisions ++
                             map (\pc -> {size=particle_mass * pc.1.spike1.1, color=pc.0.color}) particles_collisions :> [n]spike
            let spikes_additions = reduce_by_index spikes_empty spike_merge spike_empty indices values
            let new_mass = particle_mass * r32 (length particles_collisions)
            let planet_mass_goal = planet_mass pl + new_mass
            let calc_spikes (factor: f32): []spike = map2 (\s sa ->
                                                             let sa_size' = factor * sa.size
                                                             in {size=s.size + sa_size',
                                                                 color=color_merge (s.color, s.size) (sa.color, sa_size')})
                                                          pl.spikes spikes_additions
            let calc_mass (factor: f32): f32 = planet_mass' (map (.size) (calc_spikes factor))
            let (factor_lower, factor_upper) = -- finetune maybe
              (0, f32.sqrt (planet_mass_goal / f32.pi) / f32.maximum (map (.size) spikes_additions))

            let binsearch_goal_delta = 0.00001
            let max_iter = 100
            let (factor_approx, n_iters) = binary_search planet_mass_goal binsearch_goal_delta factor_lower factor_upper max_iter calc_mass
            let spikes' = calc_spikes factor_approx

            let spike_min = f32.minimum (map (.size) spikes')
            let spike_diff_factor = f32.maximum (map (.size) spikes') / spike_min
            let (spikes'', factor_approx, n_iters) =
              if spike_diff_factor <= max_spike_diff_factor
              then (spikes', factor_approx, n_iters)
              else let spikes_reshaped =
                     map (\(s: spike) ->
                            s with size = if s.size / spike_min <= max_spike_diff_factor
                                          then s.size
                                          else spike_min * max_spike_diff_factor) spikes'
                   let calc_spikes' (factor: f32): []spike =
                     map (\(s: spike) -> s with size = factor * s.size) spikes_reshaped
                   let calc_mass' (factor: f32): f32 = planet_mass' (map (.size) (calc_spikes' factor))
                   let (factor_lower', factor_upper') = (1, spike_diff_factor)
                   let (factor_reshape_approx, n_iters) =
                     binary_search planet_mass_goal binsearch_goal_delta factor_lower' factor_upper' max_iter calc_mass'
                   in (calc_spikes' factor_reshape_approx, factor_reshape_approx, n_iters)

            let debug = {factor=factor_approx,
                         factor_lower=factor_lower,
                         factor_upper=factor_upper,
                         n_iters=n_iters,
                         newly_consumed_mass=new_mass,
                         planet_mass_theoretical=planet_mass_goal,
                         spike_diff_factor}
            in (pl with spikes = spikes'', debug)

  let (planets', debugs) = unzip (map2 step_planet s.planets s.debugs) -- fixme keep debugs within planets field

  -- risk of tunneling effect, but we don't care
  let collisions = map (\part -> any (\pl -> (check_collision pl part.p).has_collision) s.planets) particles
  let (_particles_collisions, particles_unchanged) = partition (.1) (zip particles collisions)
  let particles' = map (.0) particles_unchanged
  in s with planets = planets'
       with particles = particles'
       with debugs = debugs

let xy_factor (s: state): f32 =
  r32 (i32.min s.h s.w) * s.view_zoom

let lys_render (s: state): [][]argb.colour =
  let render_planet_at (yi: i32) (xi: i32): argb.colour =
    let base = {y=r32 (yi - s.h / 2), x=r32 (xi - s.w / 2)}
    let p = vec2.scale (1 / xy_factor s) base vec2.+ s.view_center
    let planet_colors =
      map (\pl -> let c = check_collision pl p
                  in if c.has_collision
                     then let (color0, color1) = (pl.spikes[c.spike0.0].color,
                                                  pl.spikes[c.spike1.0].color)
                          in argb.mix c.spike0.1 color0 c.spike1.1 color1
                     else 0) s.planets
    in (reduce_comm (\(c0, m0) (c1, m1) -> (color_merge (c0, m0) (c1, m1), m0 + m1)) (0, 0) (zip planet_colors (map planet_mass s.planets))).0

  let particle_index ({p, pd=_, color}: particle): (i32, argb.colour) =
    let xy_fac = r32 (i32.min s.h s.w)
    let find_base = r32 <-< i32.max 0
    let offset = vec2.scale (1 / xy_fac / 2) {y=find_base (s.h - s.w), x=find_base (s.w - s.h)}
    let p' = vec2.(scale xy_fac ((scale s.view_zoom p + {y=0.5, x=0.5} + offset) - scale s.view_zoom s.view_center))
    let (y, x) = (t32 p'.y, t32 p'.x)
    in if y >= 0 && y < s.h && x >= 0 && x < s.w
       then (y * s.w + x, color)
       else (-1, 0)

  let pixels = flatten (tabulate_2d s.h s.w render_planet_at)
  let (points_indices, points_values) = unzip (map particle_index s.particles)
  let pixels = scatter pixels points_indices points_values
  in unflatten s.h s.w pixels


module lys: lys with text_content = text_content = {
  type~ state = state

  let init (seed: u32) (h: i32) (w: i32): state =
    let rng = rnge.rng_from_seed [i32.u32 seed]
    let (rng, planets) = gen_planets rng
    let (rng, particles) = gen_particles rng
    in {planets, particles,
        mouse={y=0, x=0},
        view_zoom=0.1, view_center={y=0, x=0},
        rng, h, w,
        info_idx=0,
        debugs=map debug_init planets}

  let grab_mouse = false

  let resize (h: i32) (w: i32) (s: state): state =
    s with h = h with w = w

  let zoom_at_mouse (zoom_factor: f32) (s: state): state =
    let b = {y=r32 (s.mouse.y - s.h / 2),
             x=r32 (s.mouse.x - s.w / 2)}
    let d = vec2.scale (1 / xy_factor s) b vec2.- vec2.scale (1 / (xy_factor s * zoom_factor)) b
    in s with view_zoom = s.view_zoom * zoom_factor
         with view_center = s.view_center vec2.+d

  let event (e: event) (s: state): state =
    match e
    case #step td ->
      step td s
    case #keydown {key} ->
      if key == SDLK_r
      then let (rng, planets) = gen_planets s.rng
           let (rng, particles) = gen_particles rng
           in s with planets = planets
                with particles = particles
                with rng = rng
      else if key == SDLK_1
      then s with info_idx = (s.info_idx - 1) % n_planets
      else if key == SDLK_2
      then s with info_idx = (s.info_idx + 1) % n_planets
      else s
    case #mouse {buttons, x, y} ->
      let s = if bool.i32 (buttons & 0b001)
              then let diff = {y=r32 (s.mouse.y - y),
                               x=r32 (s.mouse.x - x)}
                   in s with view_center = s.view_center vec2.+ vec2.scale (1 / xy_factor s) diff
              else s
      let s = s with mouse = {y, x}
      in s

    case #wheel {dx=_, dy} ->
      let zoom_factor = 1 + r32 dy * 0.02
      in zoom_at_mouse zoom_factor s
    case _ -> s

  let render (s: state): [][]argb.colour = lys_render s

  type text_content = text_content

  let text_format = lys_text_format

  let text_content = lys_text_content

  let text_colour = const argb.white
}
