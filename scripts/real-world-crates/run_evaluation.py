import os
import sys
import signal
import itertools
import subprocess
import threading
from multiprocessing.pool import ThreadPool

# 定义终端颜色代码，用于彩色输出
class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

# 配置变量
# 只使用第一个抽象域，以加快分析速度
abstract_domains = ["ppl_linear_congruences"]
# "linear_equalities", "ppl_polyhedra",
# "ppl_linear_congruences", "pkgrid_polyhedra_linear_congruences"]

# 获取脚本所在的目录
root_dir = os.path.dirname(os.path.abspath(__file__))
# 获取 cargo-mir-checker 可执行文件的路径
executable = os.path.abspath(os.path.join(root_dir, "../../target/release/cargo-mir-checker"))
# 输出目录路径
output_dir = os.path.join(root_dir, "output")
# 获取所有测试用例的路径（排除 output 目录）
test_cases = [os.path.abspath(i) for i in os.listdir(root_dir)
              if os.path.isdir(os.path.join(root_dir, i)) and os.path.abspath(i) != output_dir]

# 用于同步全局计数器的线程锁
lock = threading.Lock()
# 全局计数器
total_count = 0
success_count = 0
fail_count = 0
timeout_count = 0


# 定义 evaluate 函数，用于执行单个任务
def evaluate(task):
    crate_dir = task["crate_dir"]  # 项目目录
    crate_name = os.path.basename(crate_dir)  # 项目名称
    domain = task["domain"]  # 使用的抽象域
    entry = task["entry"]  # 入口函数

    # 打印任务信息
    print("Evaluating", crate_name, "with domain type:", domain, "entry function:", entry)

    # 更新全局任务总数
    if lock.acquire():
        global total_count
        total_count += 1
        lock.release()

    # 创建构建目录
    build_dir = os.path.abspath(os.path.join(crate_name, entry + "_" + domain + "_build"))
    mkdir(build_dir)

    # 运行 cargo clean，确保不使用缓存
    p = subprocess.Popen(["cargo", "clean", "--target-dir", build_dir], cwd=crate_dir)
    p.wait()

    # 运行 cargo-mir-checker
    with subprocess.Popen([executable, "mir-checker", "--target-dir", build_dir, "--", "--entry_def_id_index", entry, "--domain", domain],
                          cwd=crate_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, preexec_fn=os.setsid) as process:
        try:
            # 获取输出
            out = process.communicate(timeout=300)[0]

            # 如果返回码为 0，表示分析成功
            if process.returncode == 0:
                print(bcolors.OKBLUE, "Finish analyzing crate", crate_name, "entry function:", entry, "domain type:", domain, bcolors.ENDC)
                # 输出文件路径
                output_file_path = os.path.join(crate_name, entry + "_" + domain)
                # 将输出解码为字符串
                out_str = out.decode("utf-8")
                # 如果输出包含 MirChecker 的诊断信息，则写入文件
                if "[MirChecker]" in out_str:
                    f = open(output_file_path, "w")
                    f.write(out_str)
                    f.close()

                # 更新成功计数器
                if lock.acquire():
                    global success_count
                    success_count += 1
                    lock.release()
            else:
                # 如果返回码非 0，表示分析失败
                print(bcolors.FAIL, "Error while analyzing crate", crate_name, "entry function:", entry, "domain type:", domain, bcolors.ENDC)
                # 更新失败计数器
                if lock.acquire():
                    global fail_count
                    fail_count += 1
                    lock.release()
        except subprocess.TimeoutExpired:
            # 如果超时
            print(bcolors.FAIL, "Timeout while analyzing crate", crate_name, "entry function:", entry, "domain type:", domain, bcolors.ENDC)
            # 终止进程
            os.killpg(process.pid, signal.SIGTERM)
            # 更新超时计数器
            if lock.acquire():
                global timeout_count
                timeout_count += 1
                lock.release()

    # 清理构建目录
    print("Cleaning up", build_dir)
    p = subprocess.Popen(["rm", "-rf", build_dir], cwd=crate_dir)
    p.wait()


# 定义 mkdir 函数，用于创建目录（如果不存在）
def mkdir(dir_name):
    if not os.path.exists(dir_name):
        os.makedirs(dir_name)


# 定义 get_task_list 函数，用于生成任务列表
def get_task_list(crate_dir):
    # 如果项目目录中没有 Cargo.toml 文件，则忽略
    if not os.path.exists(os.path.join(crate_dir, "Cargo.toml")):
        return None
    crate_name = os.path.basename(crate_dir)  # 项目名称

    # 运行 cargo clean，确保不使用缓存
    p = subprocess.Popen(["cargo", "clean"], cwd=crate_dir)
    p.wait()

    # 获取入口函数列表
    p = subprocess.Popen([executable, "mir-checker", "--", "--show_entries_index"],
                         cwd=crate_dir, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    entry_functions, _ = p.communicate()
    entry_functions = list(map(lambda x: str(x, "utf-8"), entry_functions.split()))

    # 如果没有可用的入口函数，忽略该项目
    if len(entry_functions) == 0:
        print(bcolors.WARNING, crate_name, "has no usable entry points, ignored", bcolors.ENDC)
        return None
    else:
        # 生成任务列表
        result = []
        for (entry, domain) in itertools.product(entry_functions, abstract_domains):
            task = {}
            task["crate_dir"] = crate_dir
            task["entry"] = entry
            task["domain"] = domain
            result.append(task)

        # 将任务添加到全局任务列表
        if task_list_lock.acquire():
            global task_list
            if result is not None:
                task_list += result
                mkdir(crate_name)
            task_list_lock.release()


# 主程序入口
if __name__ == "__main__":
    # 检查命令行参数
    if len(sys.argv) != 2:
        print("Need an argument to specify the size of the thread pool")
        exit(1)

    # 获取线程池大小
    num_thread = int(sys.argv[1])

    # 创建输出目录并切换到该目录
    mkdir(output_dir)
    os.chdir(output_dir)

    # 定义任务列表锁
    task_list_lock = threading.Lock()
    task_list = []

    # 并行化生成任务列表
    with ThreadPool(num_thread) as p:
        p.map(get_task_list, test_cases)

    # 打印任务总数
    print(len(task_list), "tasks in total")

    # 并行化执行任务
    with ThreadPool(num_thread) as p:
        p.map(evaluate, task_list)

    # 打印最终结果
    print("Done with success:", success_count, ", fail:", fail_count, ", timeout:", timeout_count, ", total:", total_count)