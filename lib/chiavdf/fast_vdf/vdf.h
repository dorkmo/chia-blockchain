#include "include.h"

#include <x86intrin.h>

#include "parameters.h"

#include "bit_manipulation.h"
#include "double_utility.h"
#include "integer.h"

#include "asm_main.h"

#include "vdf_original.h"

#include "vdf_new.h"
#include "picosha2.h"

#include "gpu_integer.h"
#include "gpu_integer_divide.h"

#include "gcd_base_continued_fractions.h"
//#include "gcd_base_divide_table.h"
#include "gcd_128.h"
#include "gcd_unsigned.h"

#include "gpu_integer_gcd.h"

#include "asm_types.h"

#include "threading.h"
#include "nucomp.h"
#include "vdf_fast.h"

#include "vdf_test.h"
#include <map>
#include <algorithm>

#include <thread>
#include <future>

#include <chrono>
#include <condition_variable>

#include "proof_common.h"

#include <boost/asio.hpp>

bool warn_on_corruption_in_production=false;

using boost::asio::ip::tcp;

const int kMaxItersAllowed = 8e8;
// Don't modify this constant!
const int kSwitchIters = 91000000;

struct akashnil_form {
    // y = ax^2 + bxy + y^2
    mpz_t a;
    mpz_t b;
    mpz_t c;
    // mpz_t d; // discriminant
};

const int64_t THRESH = 1UL<<31;
const int64_t EXP_THRESH = 31;

form* forms;
// Notifies ProverManager class each time there's a new event.
bool new_event = false;
std::condition_variable new_event_cv;
std::mutex new_event_mutex;

bool debug_mode = true;

//always works
void repeated_square_original(vdf_original &vdfo, form& f, const integer& D, const integer& L, uint64 base, uint64 iterations, INUDUPLListener *nuduplListener) {
    vdf_original::form f_in,*f_res;
    f_in.a[0]=f.a.impl[0];
    f_in.b[0]=f.b.impl[0];
    f_in.c[0]=f.c.impl[0];
    f_res=&f_in;

    for (uint64_t i=0; i < iterations; i++) {
        f_res = vdfo.square(*f_res);

        if(nuduplListener!=NULL)
            nuduplListener->OnIteration(NL_FORM,f_res,base+i);
    }

    mpz_set(f.a.impl, f_res->a);
    mpz_set(f.b.impl, f_res->b);
    mpz_set(f.c.impl, f_res->c);
}

class WesolowskiCallback :public INUDUPLListener {
public:
    uint64_t kl;

    //struct form *forms;
    form result;

    bool deferred;
    int64_t switch_iters = -1;
    int64_t switch_index;
    int64_t iterations = 0; // This must be intialized to zero at start
    int segments;
    const int bucket_size1 = 6554;
    const int bucket_size2 = 21846;
    // Assume provers won't be left behind by more than this # of segments.
    const int window_size = 20;

    integer D;
    integer L;

    ClassGroupContext *t;
    Reducer *reducer;

    vdf_original* vdfo;

    std::vector<int> buckets_begin;

    WesolowskiCallback(int segments, integer& D) {
        vdfo = new vdf_original();
        t=new ClassGroupContext(4096);
        reducer=new Reducer(*t);
        buckets_begin.push_back(0);
        buckets_begin.push_back(bucket_size1 * window_size);
        this->segments = segments;
        for (int i = 0; i < segments - 2; i++) {
            buckets_begin.push_back(buckets_begin[buckets_begin.size() - 1] + bucket_size2 * window_size);
        }
        
        int space_needed = 20 * (21846 * (segments - 1) + 6554);
        forms = (form*) calloc(space_needed, sizeof(form));
        std::cout << "Calloc'd " << to_string(space_needed * sizeof(form)) << " bytes\n";

        this->D = D;
        this->L = root(-D, 4);
        form f = form::generator(D);
        for (int i = 0; i < segments; i++)
            forms[buckets_begin[i]] = f;
    }

    ~WesolowskiCallback() {
        delete(vdfo);
        delete(reducer);
        delete(t);
    }

    void reduce(form& inf) {
#if 0
        // Old reduce from Sundersoft form
        inf.reduce();
#else
        // Pulmark reduce based on Akashnil reduce
        mpz_set(t->a, inf.a.impl);
        mpz_set(t->b, inf.b.impl);
        mpz_set(t->c, inf.c.impl);

        reducer->run();

        mpz_set(inf.a.impl, t->a);
        mpz_set(inf.b.impl, t->b);
        mpz_set(inf.c.impl, t->c);
#endif
    }

    void IncreaseConstants(int num_iters) {
        kl = 100;
        switch_iters = num_iters;
        switch_index = num_iters / 10;
    }

    int GetPosition(int exponent, int bucket) {
        int power_2 = 1 << (16 + 2 * bucket);
        int position = buckets_begin[bucket];
        int size = (bucket == 0) ? bucket_size1 : bucket_size2;
        int kl = (bucket == 0) ? 10 : (12 * (power_2 >> 18));
        position += ((exponent / power_2) % window_size) * size;
        position += (exponent % power_2) / kl;
        return position;
    }

    form *GetForm(int exponent, int bucket) {
        return &(forms[GetPosition(exponent, bucket)]);
    }

    void SetForm(int type, void *data, form* mulf) {
        switch(type) {
            case NL_SQUARESTATE:
            {
                //cout << "NL_SQUARESTATE" << endl;
                uint64 res;

                square_state_type *square_state=(square_state_type *)data;

                if(!square_state->assign(mulf->a, mulf->b, mulf->c, res))
                    cout << "square_state->assign failed" << endl;
                break;
            }
            case NL_FORM:
            {
                //cout << "NL_FORM" << endl;

                vdf_original::form *f=(vdf_original::form *)data;

                mpz_set(mulf->a.impl, f->a);
                mpz_set(mulf->b.impl, f->b);
                mpz_set(mulf->c.impl, f->c);
                break;
            }
            default:
                cout << "Unknown case" << endl;
        }
        reduce(*mulf);
    }
    
    // We need to store: 
    // 2^16 * k + 10 * l
    // 2^(18 + 2*m) * k + 12 * 2^(2*m) * l

    void OnIteration(int type, void *data, uint64 iteration)
    {
        iteration++;
        form* mulf;
        for (int i = 0; i < segments; i++) {
            int power_2 = 1 << (16 + 2 * i);
            int kl = (i == 0) ? 10 : (12 * (power_2 >> 18));
            if ((iteration % power_2) % kl == 0) {
                mulf = GetForm(iteration, i);
                SetForm(type, data, mulf);
            }
        }
        //iterations=iteration; // safe to access now
    }
};

void ApproximateParameters(uint64_t T, uint64_t& L, uint64_t& k, uint64_t& w) {
    double log_memory = 23.25349666;
    double log_T = log2(T);
    L = 1;
    if (log_T - log_memory > 0.000001) {
        L = ceil(pow(2, log_memory - 20));
    }
    double intermediate = T * (double)0.6931471 / (2.0 * L);
    k = std::max(std::round(log(intermediate) - log(log(intermediate)) + 0.25), 1.0);
    //w = floor((double) T / ((double) T/k + L * (1 << (k+1)))) - 2;
    w = 2;
}

// thread safe; but it is only called from the main thread
void repeated_square(form f, const integer& D, const integer& L, WesolowskiCallback &weso, bool& stopped) {
    #ifdef VDF_TEST
        uint64 num_calls_fast=0;
        uint64 num_iterations_fast=0;
        uint64 num_iterations_slow=0;
    #endif

    uint64_t num_iterations = 0;

    while (!stopped) {
        uint64 c_checkpoint_interval=checkpoint_interval;

        if (weso.iterations >= kMaxItersAllowed - 500000) {
            std::cout << "Maximum possible number of iterations reached!\n";
            return ;
        }

        if (weso.iterations >= kSwitchIters && weso.kl == 10) {
            uint64 round_up = (100 - num_iterations % 100) % 100;
            if (round_up > 0) {
                repeated_square_original(*weso.vdfo, f, D, L, num_iterations, round_up, &weso);
            }
            num_iterations += round_up;
            weso.IncreaseConstants(num_iterations);
        }

        #ifdef VDF_TEST
            form f_copy;
            form f_copy_3;
            bool f_copy_3_valid=false;
            if (vdf_test_correctness) {
                f_copy=f;
                c_checkpoint_interval=1;

                f_copy_3=f;
                f_copy_3_valid=square_fast_impl(f_copy_3, D, L, num_iterations);
            }
        #endif

        uint64 batch_size=c_checkpoint_interval;

        #ifdef ENABLE_TRACK_CYCLES
            print( "track cycles enabled; results will be wrong" );
            repeated_square_original(*weso.vdfo, f, D, L, 100); //randomize the a and b values
        #endif

        // This works single threaded
        square_state_type square_state;
        square_state.pairindex=0;

        uint64 actual_iterations=repeated_square_fast(square_state, f, D, L, num_iterations, batch_size, &weso);

        #ifdef VDF_TEST
            ++num_calls_fast;
            if (actual_iterations!=~uint64(0)) num_iterations_fast+=actual_iterations;
        #endif

        #ifdef ENABLE_TRACK_CYCLES
            print( "track cycles actual iterations", actual_iterations );
            return; //exit the program
        #endif

        if (actual_iterations==~uint64(0)) {
            //corruption; f is unchanged. do the entire batch with the slow algorithm
            repeated_square_original(*weso.vdfo, f, D, L, num_iterations, batch_size, &weso);
            actual_iterations=batch_size;

            #ifdef VDF_TEST
                num_iterations_slow+=batch_size;
            #endif

            if (warn_on_corruption_in_production) {
                print( "!!!! corruption detected and corrected !!!!" );
            }
        }

        if (actual_iterations<batch_size) {
            //the fast algorithm terminated prematurely for whatever reason. f is still valid
            //it might terminate prematurely again (e.g. gcd quotient too large), so will do one iteration of the slow algorithm
            //this will also reduce f if the fast algorithm terminated because it was too big
            repeated_square_original(*weso.vdfo, f, D, L, num_iterations+actual_iterations, 1, &weso);

#ifdef VDF_TEST
                ++num_iterations_slow;
                if (vdf_test_correctness) {
                    assert(actual_iterations==0);
                    print( "fast vdf terminated prematurely", num_iterations );
                }
            #endif

            ++actual_iterations;
        }

        if (num_iterations % (1 << 16) + actual_iterations >= (1 << 16)) {
            //if (debug_mode) {
            //    std::cout << "VDF Worker iteration: " << (num_iterations + actual_iterations) << "\n";
            //}
            // Notify event loop a new segment arrives.
            std::lock_guard<std::mutex> lk(new_event_mutex);
            new_event = true;
            new_event_cv.notify_one();
        }
        num_iterations+=actual_iterations;
        weso.iterations = num_iterations;
        #ifdef VDF_TEST
            if (vdf_test_correctness) {
                form f_copy_2=f;
                weso.reduce(f_copy_2);

                repeated_square_original(&weso.vdfo, f_copy, D, L, actual_iterations);
                assert(f_copy==f_copy_2);
            }
        #endif
    }

    if (debug_mode) {
        std::cout << "Final number of iterations: " << num_iterations << "\n";
    }
    #ifdef VDF_TEST
        print( "fast average batch size", double(num_iterations_fast)/double(num_calls_fast) );
        print( "fast iterations per slow iteration", double(num_iterations_fast)/double(num_iterations_slow) );
    #endif
}

uint64_t GetBlock(uint64_t i, uint64_t k, uint64_t T, integer& B) {
    integer res = FastPow(2, T - k * (i + 1), B);
    mpz_mul_2exp(res.impl, res.impl, k);
    res = res / B;
    auto res_vector = res.to_vector();
    return res_vector[0];
}

std::string BytesToStr(const std::vector<unsigned char> &in)
{
    std::vector<unsigned char>::const_iterator from = in.cbegin();
    std::vector<unsigned char>::const_iterator to = in.cend();
    std::ostringstream oss;
    for (; from != to; ++from)
       oss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(*from);
    return oss.str();
}

struct Proof {
    Proof() {

    }

    Proof(std::vector<unsigned char> y, std::vector<unsigned char> proof) {
        this->y = y;
        this->proof = proof;
    }

    string hex() {
        std::vector<unsigned char> bytes(y);
        bytes.insert(bytes.end(), proof.begin(), proof.end());
        return BytesToStr(bytes);
    }

    std::vector<unsigned char> y;
    std::vector<unsigned char> proof;
};

form GenerateProof(form &y, form &x_init, integer &D, uint64_t done_iterations, uint64_t num_iterations, uint64_t k, uint64_t l, WesolowskiCallback& weso, bool& stop_signal) {
}

void GenerateProofThreaded(std::promise<form> && form_promise, form y, form x_init, integer D, uint64_t done_iterations, uint64_t num_iterations, uint64_t
k, uint64_t l, WesolowskiCallback& weso, bool& stop_signal) {
    form proof = GenerateProof(y, x_init, D, done_iterations, num_iterations, k, l, weso, stop_signal);
    form_promise.set_value(proof);
}

Proof CreateProofOfTimeWesolowski(integer& D, form x, int64_t num_iterations, uint64_t done_iterations, WesolowskiCallback& weso, bool& stop_signal) {
    uint64_t l, k, w;
    form x_init = x;
    integer L=root(-D, 4);

    k = 10;
    w = 2;
    l = (num_iterations >= 10000000) ? 10 : 1;

    while (!stop_signal && weso.iterations < done_iterations + num_iterations) {
        std::this_thread::sleep_for (std::chrono::milliseconds(200));
    }

    if (stop_signal)
        return Proof();

    vdf_original vdfo_proof;

    uint64 checkpoint = (done_iterations + num_iterations) - (done_iterations + num_iterations) % 100;
    //mpz_init(y.a.impl);
    //mpz_init(y.b.impl);
    //mpz_init(y.c.impl);
    form y;
    repeated_square_original(vdfo_proof, y, D, L, 0, (done_iterations + num_iterations) % 100, NULL);

    auto proof = GenerateProof(y, x_init, D, done_iterations, num_iterations, k, l, weso, stop_signal);

    if (stop_signal)
        return Proof();

    int int_size = (D.num_bits() + 16) >> 4;

    std::vector<unsigned char> y_bytes = SerializeForm(y, 129);

    std::vector<unsigned char> proof_bytes = SerializeForm(proof, int_size);
    Proof final_proof=Proof(y_bytes, proof_bytes);
    return final_proof;
}

Proof CreateProofOfTimeNWesolowski(integer& D, form x, int64_t num_iterations,
                                   uint64_t done_iterations, WesolowskiCallback& weso, int depth_limit, int depth, bool& stop_signal) {
    uint64_t l, k, w;
    int64_t iterations1, iterations2;
    integer L=root(-D, 4);
    form x_init = x;

    k = 10;
    w = 2;
    iterations1 = num_iterations * w / (w + 1);

    // NOTE(Florin): This is still suboptimal,
    // some work can still be lost if weso iterations is in between iterations1 and num_iterations.
    if (weso.iterations >= done_iterations + num_iterations) {
        iterations1 = (done_iterations + num_iterations) / 3;
    }

    iterations1 = iterations1 - iterations1 % 100;
    iterations2 = num_iterations - iterations1;

    l = (iterations1 >= 10000000) ? 10 : 1;
    
    while (!stop_signal && weso.iterations < done_iterations + iterations1) {
        std::this_thread::sleep_for (std::chrono::milliseconds(200));
    }

    if (stop_signal)
        return Proof();

    form y1;

    std::promise<form> form_promise;
    auto form_future = form_promise.get_future();

    std::thread t(&GenerateProofThreaded, std::move(form_promise), y1, x_init, D, done_iterations, iterations1, k, l, std::ref(weso), std::ref(stop_signal));

    Proof proof2;
    if (depth < depth_limit - 1) {
        proof2 = CreateProofOfTimeNWesolowski(D, y1, iterations2, done_iterations + iterations1, weso, depth_limit, depth + 1, stop_signal);
    } else {
        proof2 = CreateProofOfTimeWesolowski(D, y1, iterations2, done_iterations + iterations1, weso, stop_signal);
    }

    t.join();
    if (stop_signal)
        return Proof();
    form proof = form_future.get();

    int int_size = (D.num_bits() + 16) >> 4;
    Proof final_proof;
    final_proof.y = proof2.y;
    std::vector<unsigned char> proof_bytes(proof2.proof);
    std::vector<unsigned char> tmp = ConvertIntegerToBytes(integer(iterations1), 8);
    proof_bytes.insert(proof_bytes.end(), tmp.begin(), tmp.end());
    tmp.clear();
    tmp = SerializeForm(y1, int_size);
    proof_bytes.insert(proof_bytes.end(), tmp.begin(), tmp.end());
    tmp.clear();
    tmp = SerializeForm(proof, int_size);
    proof_bytes.insert(proof_bytes.end(), tmp.begin(), tmp.end());
    final_proof.proof = proof_bytes;
    return final_proof;
}

struct Segment {
    uint64_t start;
    uint64_t length;
    form x;
    form y;
    form proof;
    bool is_empty;

    Segment() {
        is_empty = true;
    }

    Segment(uint64_t start, uint64_t length, form& x, form& y) {        
        this->start = start;
        this->length = length;
        this->x = x;
        this->y = y;
        is_empty = false;
    }

    bool IsWorseThan(Segment& other) {
        if (is_empty) {
            if (!other.is_empty)
                return true;
            return false;
        }
        if (length > other.length)
            return true;
        if (length < other.length)  
            return false;
        return start > other.start;
    }

    int GetSegmentBucket() {
        int c_length = length;
        length >>= 16;
        int index = 0;
        while (length > 1) {
            index++;
            if (length == 2 || length == 3) {
                std::cout << "Warning: Invalid segment length.\n";
            }
            length >>= 2;
        }
        length = c_length;
        return index;
    }
};

class Prover {
  public:
    Prover(Segment& segm, integer& D, WesolowskiCallback* weso) {
        this->y = segm.y;
        this->x_init = segm.x;
        this->D = D;
        this->bucket = segm.GetSegmentBucket();
        this->done_iterations = segm.start;
        this->num_iterations = segm.length;
        if (segm.length <= (1 << 16))
            this->k = 10;
        else
            this->k = 12;
        if (segm.length <= (1 << 18)) {
            this->l = 1;
        } else {
            this->l = (segm.length >> 18);
        }
        this->weso = weso;
        is_paused = false;
        is_finished = false;
    }

    void stop() {
        std::lock_guard<std::mutex> lk(m);
        is_finished = true;
        if (is_paused) {
            is_paused = false;
            cv.notify_one();
        }
    }

    void start() {
        std::thread t([=] { GenerateProof(); });
        t.detach();
    }

    void pause() {
        std::lock_guard<std::mutex> lk(m);
        is_paused = true;
    }

    void resume() {
        std::lock_guard<std::mutex> lk(m);
        is_paused = false;
        cv.notify_one();
    }

    bool IsRunning() {
        return !is_paused;
    }

    bool IsFinished() {
        return is_finished;
    }

    form GetProof() {
        return proof;
    }

    void GenerateProof() {
        auto t1 = std::chrono::high_resolution_clock::now();

        PulmarkReducer reducer;

        integer B = GetB(D, x_init, y);
        integer L=root(-D, 4);

        uint64_t k1 = k / 2;
        uint64_t k0 = k - k1;

        form x = form::identity(D);

        for (int64_t j = l - 1; j >= 0; j--) {
            x = FastPowFormNucomp(x, D, integer(1 << k), L, reducer);

            std::vector<form> ys((1 << k));
            for (uint64_t i = 0; i < (1 << k); i++)
                ys[i] = form::identity(D);

            form *tmp;
            for (uint64_t i = 0; i < ceil(1.0 * num_iterations / (k * l)); i++) {
                if (num_iterations >= k * (i * l + j + 1)) {
                    uint64_t b = GetBlock(i*l + j, k, num_iterations, B);
                    tmp = weso->GetForm(done_iterations + i * k * l, bucket);
                    nucomp_form(ys[b], ys[b], *tmp, D, L);
                }
                if (is_finished) {
                    return ;
                }
                while (is_paused) {
                    std::unique_lock<std::mutex> lk(m);
                    cv.wait(lk);
                    lk.unlock();
                }
            }

            for (uint64_t b1 = 0; b1 < (1 << k1); b1++) {
                form z = form::identity(D);
                for (uint64_t b0 = 0; b0 < (1 << k0); b0++) {
                    nucomp_form(z, z, ys[b1 * (1 << k0) + b0], D, L);
                    if (is_finished) {
                        return;
                    }
                    while (is_paused) {
                        std::unique_lock<std::mutex> lk(m);
                        cv.wait(lk);
                        lk.unlock();
                    }
                }
                z = FastPowFormNucomp(z, D, integer(b1 * (1 << k0)), L, reducer);
                nucomp_form(x, x, z, D, L);
            }

            for (uint64_t b0 = 0; b0 < (1 << k0); b0++) {
                form z = form::identity(D);
                for (uint64_t b1 = 0; b1 < (1 << k1); b1++) {
                    nucomp_form(z, z, ys[b1 * (1 << k0) + b0], D, L);
                    if (is_finished) {
                        return ;
                    }
                    while (is_paused) {
                        std::unique_lock<std::mutex> lk(m);
                        cv.wait(lk);
                        lk.unlock();
                    }
                }
                z = FastPowFormNucomp(z, D, integer(b0), L, reducer);
                nucomp_form(x, x, z, D, L);
            }
        }

        reducer.reduce(x);

        auto t2 = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
        proof = x;
        is_finished = true;
        // Notify event loop a proving thread is free.
        std::lock_guard<std::mutex> lk(new_event_mutex);
        new_event = true;
        new_event_cv.notify_one();
    }

  private:
    form y;
    form x_init;
    form proof;
    integer D;
    uint64_t num_iterations;
    uint64_t k;
    uint64_t done_iterations;
    uint64_t l;
    int bucket;
    WesolowskiCallback* weso;
    bool is_paused;
    bool is_finished;
    std::condition_variable cv;
    std::mutex m;
};

class ProverManager {
  public:
    ProverManager(integer& D, WesolowskiCallback* weso, int segment_count, int max_proving_threads) {
        this->segment_count = segment_count;
        this->max_proving_threads = max_proving_threads;
        this->D = D;
        this->weso = weso;
        std::vector<Segment> tmp;
        for (int i = 0; i < segment_count; i++) {
            pending_segments.push_back(tmp);
            done_segments.push_back(tmp);
            last_appended.push_back(0);
        }
    }

    void start() {
        std::thread t([=] {RunEventLoop(); });
        t.detach();
    }

    void stop() {        
        stopped = true;
        for (int i = 0; i < provers.size(); i++)
            provers[i].first->stop();
    }

    void RunEventLoop() {
        while (!stopped) {
            // Wait for some event to happen.
            {
                std::unique_lock<std::mutex> lk(new_event_mutex);
                new_event_cv.wait(lk, []{return new_event;});
                new_event = false;
            }
            if (stopped)
                return; 
            // Check if some provers finished.
            for (int i = 0; i < provers.size(); i++) {
                if (provers[i].first->IsFinished()) {
                    provers[i].second.proof = provers[i].first->GetProof();
                    if (debug_mode) {
                        // Check if the segment is correct.
                        std::cout << "Done segment: [" << provers[i].second.start 
                                  << ", " << provers[i].second.start + provers[i].second.length 
                                  << "]. Bucket: " << provers[i].second.GetSegmentBucket() << ". ";
                        bool correct;
                        VerifyWesolowskiProof(D, provers[i].second.x, provers[i].second.y, provers[i].second.proof, provers[i].second.length, correct);
                        std::cout << (correct ? "Correct segment" : "Incorrect segment");
                        std::cout << "\n";
                    }
                    int index = provers[i].second.GetSegmentBucket();
                    done_segments[index].emplace_back(provers[i].second);
                    provers.erase(provers.begin() + i);
                    i--;
                }
            }
            // Check if new segments have arrived, and add them as pending proof.
            uint64_t vdf_iteration = weso->iterations;
            for (int i = 0; i < segment_count; i++) {
                int sg_length = 1 << (16 + 2 * i); 
                while (last_appended[i] + sg_length <= vdf_iteration) {
                    Segment sg(
                        /*start=*/last_appended[i], 
                        /*length=*/sg_length, 
                        /*x=*/*(weso->GetForm(last_appended[i], i)), 
                        /*y=*/*(weso->GetForm(last_appended[i] + sg_length, i))
                    );
                    pending_segments[i].emplace_back(sg);
                    last_appended[i] += sg_length;
                }
            }
            // If we have free proving threads, use them first.
            int active_provers = 0;
            for (int i = 0; i < provers.size(); i++) {
                if (provers[i].first->IsRunning())
                    active_provers++;
            }

            while (true) {
                // Find the best pending/paused segment and remember where it is.
                Segment best;
                int index;
                bool new_segment;
                for (int i = 0; i < provers.size(); i++) {
                    if (!provers[i].first->IsRunning()) {
                        if (best.IsWorseThan(provers[i].second)) {
                            best = provers[i].second;
                            index = i;
                            new_segment = false;
                        }
                    }
                }
                for (int i = 0; i < segment_count; i++) {
                    if (pending_segments[i].size() > 0) {
                        if (best.IsWorseThan(pending_segments[i][0])) {
                            best = pending_segments[i][0];
                            index = i;
                            new_segment = true;
                        }
                    }
                }
                // If nothing to run, stop.
                if (best.is_empty)
                    break;
                bool spawn_best = false;
                // If we have free threads, use them.
                if (active_provers < max_proving_threads) {
                    spawn_best = true;
                    active_provers++;
                } else {
                    // Otherwise, pause one already running segment, if candidate is better.
                    Segment worst_running;
                    int worst_index;
                    for (int i = 0; i < provers.size(); i++) 
                        if (provers[i].first->IsRunning()) {
                            if (worst_running.is_empty == true || provers[i].second.IsWorseThan(worst_running)) {
                                worst_running = provers[i].second;
                                worst_index = i;
                            }
                        }
                    // If the candidate is better than worst running, stop worst running and spawn candidate.
                    if (worst_running.IsWorseThan(best)) {
                        spawn_best = true;
                        provers[worst_index].first->pause();
                    }
                }
                // Best provers are already running, nothing will change until a new event happens.
                if (!spawn_best) {
                    break;
                }
                // Spawn the best segment.
                if (!new_segment) {
                    provers[index].first->resume();
                } else {
                    provers.emplace_back(
                        std::make_pair(
                            std::make_unique<Prover>(best, D, weso),                            
                            best
                        )
                    );
                    provers[provers.size() - 1].first->start();
                    pending_segments[index].erase(pending_segments[index].begin());
                }
            }
        }
    }

  private:
    bool stopped = false;
    int segment_count;
    // Maximum amount of proving threads running at once.
    int max_proving_threads;
    WesolowskiCallback* weso;
    // The discriminant used.
    integer D;
    // Active or paused provers currently running.
    std::vector<std::pair<std::unique_ptr<Prover>, Segment>> provers;
    // Vectors of segments needing proving, for each segment length. 
    std::vector<std::vector<Segment>> pending_segments;
    // For each segment length, remember the endpoint of the last segment marked as pending.
    std::vector<uint64_t> last_appended;
    // Finished segments.
    std::vector<std::vector<Segment>> done_segments;
};

